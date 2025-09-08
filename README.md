# Parser
import re
import json
import glob
import ast
import networkx as nx
import matplotlib.pyplot as plt

# -------------------------------
# Advanced Compute Expression Parser
# -------------------------------
def parse_compute_expression(target, expr, control_context, graph):
    expr_mod = re.sub(r'([\w-]+)', r'_\1', expr)
    tree = ast.parse(expr_mod, mode='eval')

    def walk(node, result_target):
        if isinstance(node, ast.BinOp):
            left = walk(node.left, result_target+"_L") if not isinstance(node.left, ast.Name) else node.left.id
            right = walk(node.right, result_target+"_R") if not isinstance(node.right, ast.Name) else node.right.id
            if isinstance(node.op, ast.Add):
                op = "ADD"
            elif isinstance(node.op, ast.Sub):
                op = "SUB"
            elif isinstance(node.op, ast.Mult):
                op = "MUL"
            elif isinstance(node.op, ast.Div):
                op = "DIV"
            else:
                op = "UNKNOWN"
            src_left = left.replace("_", "")
            src_right = right.replace("_", "")
            tgt = result_target.replace("_", "")
            graph.add_edge(src_left, tgt, op=op, ctx=list(control_context))
            graph.add_edge(src_right, tgt, op=op, ctx=list(control_context))
            return tgt
        elif isinstance(node, ast.Name):
            return node.id
        elif isinstance(node, ast.Constant):
            return str(node.value)
        else:
            return "UNKNOWN"

    walk(tree.body, target)

# -------------------------------
# COBOL Lineage Extractor
# -------------------------------
class CobolLineageExtractor:
    def __init__(self, cobol_code: str):
        self.code = cobol_code
        self.graph = nx.DiGraph()
        self.cursor_queries = {}

    # Reference modification parser
    def parse_refmod(self, expr):
        m = re.match(r"([\w-]+)\(([\w-]+):([\w-]+)\)", expr)
        if m:
            field, start, length = m.groups()
            return {"field": f"{field}({start}:{length})", "base": field, "start": start, "length": length}
        return {"field": expr, "base": expr, "start": None, "length": None}

    def add_refmod_edges(self, info, dest, op, ctx):
        self.graph.add_edge(info["base"], dest, op=op, ctx=list(ctx))
        if info["start"]:
            self.graph.add_edge(info["start"], dest, op="REFMOD-START", ctx=list(ctx))
        if info["length"]:
            self.graph.add_edge(info["length"], dest, op="REFMOD-LENGTH", ctx=list(ctx))

    # -------------------------------
    # Main parser
    # -------------------------------
    def parse(self):
        lines = iter(self.code.splitlines())
        control_context = []

        for line in lines:
            line = line.strip()
            if not line: continue

            # --- Control flow ---
            if line.upper().startswith("EVALUATE"):
                control_context.append("EVALUATE")
                continue
            if line.upper().startswith("WHEN"):
                cond = line.split(" ", 1)[-1]
                control_context.append(f"WHEN {cond}")
                continue
            m = re.match(r"IF\s+(.+)", line, re.I)
            if m:
                control_context.append(f"IF {m.group(1)}")
                continue
            m = re.match(r"PERFORM\s+([\w-]+)", line, re.I)
            if m:
                para_name = m.group(1)
                control_context.append(f"PERFORM {para_name} [loop]")
                continue

            # --- MOVE ---
            m = re.match(r"MOVE\s+([\w-]+(?:\([\w-]+:[\w-]+\))?)\s+TO\s+([\w-]+(?:\([\w-]+:[\w-]+\))?)", line, re.I)
            if m:
                src_info, dest_info = self.parse_refmod(m.group(1)), self.parse_refmod(m.group(2))
                self.add_refmod_edges(src_info, dest_info["field"], "ASSIGN", control_context)
                continue

            # --- COMPUTE ---
            m = re.match(r"COMPUTE\s+([\w-]+)\s*=\s*(.+)", line, re.I)
            if m:
                dest, rhs = m.groups()
                parse_compute_expression(dest, rhs, control_context, self.graph)
                continue

            # --- ADD / SUBTRACT / MULTIPLY / DIVIDE ---
            m = re.match(r"ADD\s+(.+)\s+TO\s+([\w-]+)", line, re.I)
            if m:
                sources, dest = m.groups()
                for src in re.findall(r"[\w-]+", sources):
                    self.graph.add_edge(src, dest, op="ADD", ctx=list(control_context))
                continue
            m = re.match(r"SUBTRACT\s+(.+)\s+FROM\s+([\w-]+)", line, re.I)
            if m:
                sources, dest = m.groups()
                for src in re.findall(r"[\w-]+", sources):
                    self.graph.add_edge(src, dest, op="SUB", ctx=list(control_context))
                continue
            m = re.match(r"MULTIPLY\s+([\w-]+)\s+BY\s+([\w\.\-]+)(?:\s+GIVING\s+([\w-]+))?", line, re.I)
            if m:
                src, factor, dest = m.groups()
                if not dest:
                    dest = src
                self.graph.add_edge(src, dest, op="MUL", ctx=list(control_context))
                self.graph.add_edge(factor, dest, op="MUL", ctx=list(control_context))
                continue
            m = re.match(r"DIVIDE\s+([\w-]+)\s+BY\s+([\w\.\-]+)(?:\s+GIVING\s+([\w-]+))?", line, re.I)
            if m:
                src, divisor, dest = m.groups()
                if not dest:
                    dest = src
                self.graph.add_edge(src, dest, op="DIV", ctx=list(control_context))
                self.graph.add_edge(divisor, dest, op="DIV", ctx=list(control_context))
                continue

            # --- STRING / UNSTRING ---
            m = re.match(r"STRING\s+(.+)\s+INTO\s+([\w-]+)", line, re.I)
            if m:
                parts, dest = m.groups()
                for src in re.findall(r"[\w-]+(?:\([\w-]+:[\w-]+\))?", parts):
                    self.add_refmod_edges(self.parse_refmod(src), dest, "CONCAT", control_context)
                continue
            m = re.match(r"UNSTRING\s+([\w-]+)\s+INTO\s+(.+)", line, re.I)
            if m:
                src, targets = m.groups()
                for dest in re.findall(r"[\w-]+", targets):
                    self.add_refmod_edges(self.parse_refmod(src), dest, "SPLIT", control_context)
                continue

            # --- READ ---
            m = re.match(r"READ\s+([\w-]+)\s+INTO\s+([\w-]+)", line, re.I)
            if m:
                file, dest = m.groups()
                self.graph.add_edge(f"{file}.record", dest, op="READ-ASSIGN", ctx=list(control_context))
                continue

            # --- SQL DECLARE CURSOR / FETCH ---
            m = re.match(r"EXEC\s+SQL\s+DECLARE\s+(\w+)\s+CURSOR\s+FOR\s+(.+?)END-EXEC", line, re.I | re.S)
            if m:
                cursor_name, query = m.groups()
                self.cursor_queries[cursor_name] = query
                continue
            m = re.match(r"EXEC\s+SQL\s+FETCH\s+(\w+)\s+INTO\s+:(.+?)END-EXEC", line, re.I)
            if m:
                cursor_name, dests = m.groups()
                dests = [d.strip().replace(":", "") for d in dests.split(",")]
                query = self.cursor_queries.get(cursor_name, "")
                cols_match = re.search(r"SELECT\s+(.+?)\s+FROM", query, re.I | re.S)
                table_match = re.search(r"FROM\s+([\w\s,]+)", query, re.I | re.S)
                if cols_match and table_match:
                    columns = [c.strip() for c in cols_match.group(1).split(",")]
                    tables = [t.strip() for t in table_match.group(1).split(",")]
                    for col, dest in zip(columns, dests):
                        table = tables[0]
                        self.graph.add_edge(f"{table}.{col}", dest, op="SQL-FETCH", ctx=list(control_context))
                continue

            # --- SQL SELECT INTO (standalone) ---
            m = re.match(r"EXEC\s+SQL\s+SELECT\s+(.+?)\s+INTO\s+(.+?)\s+FROM\s+([\w]+)(?:\s+WHERE\s+(.+?))?END-EXEC", line, re.I | re.S)
            if m:
                columns, dests, table, where_clause = m.groups()
                columns = [c.strip() for c in columns.split(",")]
                dests = [d.strip().replace(":", "") for d in dests.split(",")]
                for col, dest in zip(columns, dests):
                    ctx = list(control_context)
                    if where_clause:
                        ctx.append(f"WHERE {where_clause.strip()}")
                    self.graph.add_edge(f"{table}.{col}", dest, op="SQL-SELECT", ctx=ctx)
                continue

            # --- SQL INSERT ---
            m = re.match(r"EXEC\s+SQL\s+INSERT\s+INTO\s+([\w]+)\s*\((.+?)\)\s*VALUES\s*\((.+?)\)END-EXEC", line, re.I | re.S)
            if m:
                table_name, cols, vals = m.groups()
                columns = [c.strip() for c in cols.split(",")]
                values = [v.strip().replace(":", "") for v in vals.split(",")]
                for col, val in zip(columns, values):
                    self.graph.add_edge(val, f"{table_name}.{col}", op="SQL-INSERT", ctx=list(control_context))
                continue

            # --- SQL UPDATE ---
            m = re.match(r"EXEC\s+SQL\s+UPDATE\s+([\w]+)\s+SET\s+(.+?)\s+WHERE\s+(.+?)END-EXEC", line, re.I | re.S)
            if m:
                table_name, set_clause, where_clause = m.groups()
                assignments = [a.strip() for a in set_clause.split(",")]
                for assign in assignments:
                    col, val = [x.strip() for x in assign.split("=")]
                    val = val.replace(":", "")
                    self.graph.add_edge(val, f"{table_name}.{col}", op="SQL-UPDATE", ctx=list(control_context) + [f"WHERE {where_clause.strip()}"])
                continue

    # -------------------------------
    # Lineage traversal
    # -------------------------------
    def lineage_tree(self, target: str):
        def dfs(node, visited):
            preds = self.graph.in_edges(node, data=True)
            if not preds:
                return {"field": node, "sources": []}
            sources = []
            for src, _, attrs in preds:
                if src not in visited:
                    sources.append({
                        "field": src,
                        "operation": attrs.get("op"),
                        "context": attrs.get("ctx", []),
                        "sources": dfs(src, visited | {src})["sources"]
                    })
            return {"field": node, "sources": sources}
        return dfs(target, {target})

    def export_json(self, target: str):
        return json.dumps(self.lineage_tree(target), indent=2)

# -------------------------------
# Multi-Program Orchestrator
# -------------------------------
class MultiProgramLineageExtractor:
    def __init__(self, cobol_folder):
        self.cobol_folder = cobol_folder
        self.global_graph = nx.DiGraph()
        self.program_extractors = {}

    def parse_all_programs(self):
        for filename in glob.glob(f"{self.cobol_folder}/*.cbl"):
            prog_name = filename.split("/")[-1].replace(".cbl", "")
            with open(filename, "r") as f:
                code = f.read()
            extractor = CobolLineageExtractor(code)
            extractor.parse()
            self.program_extractors[prog_name] = extractor
            self.global_graph.update(extractor.graph)

    def export_json(self, target: str):
        extractor = CobolLineageExtractor("")
        extractor.graph = self.global_graph
        return extractor.export_json(target)

    def visualize_graph(self, title="COBOL Data Lineage Graph"):
        G = self.global_graph
        pos = nx.spring_layout(G, seed=42)
        plt.figure(figsize=(16,14))
        nx.draw_networkx_nodes(G, pos, node_size=2500, node_color="lightblue", edgecolors="black")
        nx.draw_networkx_labels(G, pos, font_size=10, font_weight="bold")
        nx.draw_networkx_edges(G, pos, arrowstyle="->", arrowsize=20)
        edge_labels = {(u,v): f"{d['op']} | {', '.join(d['ctx'])}" for u,v,d in G.edges(data=True)}
        nx.draw_networkx_edge_labels(G, pos, edge_labels=edge_labels, font_size=9)
        plt.title(title, fontsize=16, fontweight="bold")
        plt.axis("off")
        plt.show()
