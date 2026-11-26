"""Terminal graphs retain every edge, including joins, cycles and branch labels."""
import json
from pathlib import Path
import tempfile
import unittest

from Skel import watch, watch_graph, watch_jobs
from Coordinator.watch import cell_width


def raw_graph():
    return {"version": 1, "functions": [
        {"id": "caller", "label": "caller-label", "callees": ["leaf", "other"], "error": "",
         "blocks": [{"id": "entry", "offset": 0, "kind": "branch"},
                    {"id": "loop", "offset": 8, "kind": "branch"},
                    {"id": "$return", "offset": None, "kind": "return"}],
         "edges": [{"from": "entry", "to": "loop", "label": "true"},
                   {"from": "entry", "to": "$return", "label": "false"},
                   {"from": "loop", "to": "loop", "label": "true"},
                   {"from": "loop", "to": "$return", "label": "false"}]},
        {"id": "other", "label": "other-label", "callees": ["leaf"], "error": "", "blocks": [], "edges": []},
        {"id": "leaf", "label": "leaf-label", "callees": [], "error": "", "blocks": [], "edges": []}]}


class GraphTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.run = Path(self.temp.name)

    def read(self, value):
        (self.run / "graph.json").write_text(json.dumps(value))
        return watch_graph.read_graph(self.run)

    def test_call_graph_retains_shared_callee_edges(self):
        graph = self.read(raw_graph())
        rows = watch_graph.call_rows(graph)
        self.assertEqual([r.node for r in rows], ["caller", "leaf", "other", "leaf"])
        self.assertEqual(rows[-1].reference, "shared")
        self.assertTrue(any("├" in r.prefix for r in rows))
        self.assertTrue(any("└" in r.prefix for r in rows))

    def test_cfg_retains_branches_cycles_and_joins(self):
        graph = self.read(raw_graph())
        rows = watch_graph.cfg_rows(graph, "caller")
        self.assertEqual(len(rows), 5)  # root plus each of the four edges
        self.assertEqual(sum(r.edge == "true" for r in rows), 2)
        self.assertEqual(sum(r.edge == "false" for r in rows), 2)
        self.assertEqual({r.reference for r in rows}, {"", "loop", "shared"})

    def test_call_cycles_external_callees_and_disconnected_nodes_are_visible(self):
        value = raw_graph()
        value["functions"][2]["callees"] = ["caller", "external"]
        rows = watch_graph.call_rows(self.read(value))
        self.assertIn("external", [r.node for r in rows])
        self.assertIn("loop", [r.reference for r in rows])
        self.assertIn("other", [r.node for r in rows])

    def test_invalid_graph_is_not_guessed(self):
        self.assertIsNone(watch_graph.read_graph(self.run))
        duplicate = raw_graph()
        duplicate["functions"].append(duplicate["functions"][0])
        missing = raw_graph()
        missing["functions"][0]["edges"][0]["to"] = "absent"
        malformed = raw_graph()
        malformed["functions"][0]["blocks"][0]["offset"] = True
        for value in [None, [], {}, {"version": 2, "functions": []}, duplicate, missing, malformed]:
            with self.subTest(value=value): self.assertIsNone(self.read(value))

    def test_terminal_graph_shows_status_and_does_not_claim_composition(self):
        graph = self.read(raw_graph())
        row = watch.Row("leaf", "block.entry", "closed", "tactics")
        ask = watch_jobs.Ask(4, "caller", "loop.loop", "test", "loop proposal", "cfg", 1)
        view = watch.View(run=self.run, graph=graph, rows={(row.fn, row.name): row}, asks=(ask,))
        for mode in ("deps", "cfg"):
            text = "\n".join(x.text for x in watch.render_graph(view, 160, 40, mode, fn="caller"))
            self.assertIn("caller", text)
            self.assertIn("[*]", text)
            self.assertIn("Final ledger is pending", text)
        deps = "\n".join(x.text for x in watch.render_graph(view, 160, 40, "deps"))
        self.assertIn("[+] leaf", deps)

    def test_small_terminals_horizontal_pan_and_absent_graph(self):
        graph = self.read(raw_graph())
        for width, height in [(0, 0), (1, 1), (10, 8), (80, 24), (140, 40)]:
            for mode in ("deps", "cfg"):
                for value in (None, graph):
                    with self.subTest(width=width, height=height, mode=mode):
                        view = watch.View(run=self.run, graph=value)
                        lines = watch.render_graph(view, width, height, mode, fn="caller", horizontal=8)
                        self.assertLessEqual(len(lines), height)
                        self.assertTrue(all(cell_width(x.text) <= width for x in lines))

    def test_monitor_reads_graph_without_writes(self):
        self.read(raw_graph())
        before = (self.run / "graph.json").read_bytes()
        view = watch.Monitor(self.run, root=self.run).refresh()
        self.assertEqual(len(view.graph.functions), 3)
        self.assertEqual((self.run / "graph.json").read_bytes(), before)

    def test_navigation_enters_selected_function_cfg_and_returns(self):
        view = watch.View(graph=self.read(raw_graph()))
        state = watch.Navigation(mode="deps", selected=2)
        cfg = watch.navigate(state, "enter", view, 10)
        self.assertEqual((cfg.mode, cfg.fn, cfg.selected), ("cfg", "other", 0))
        back = watch.navigate(cfg, "back", view, 10)
        self.assertEqual(back.mode, "deps")
        self.assertEqual(watch.graph_items(view, back)[back.selected].node, "other")
        self.assertEqual(watch.navigate(cfg, "next_fn", view, 10).fn, "leaf")
        self.assertEqual(watch.navigate(state, "tab", view, 10).mode, "cfg")

    def test_navigation_clamps_selection_and_pan_and_ignores_other_keys(self):
        view = watch.View(graph=self.read(raw_graph()))
        state = watch.Navigation(mode="deps")
        self.assertEqual(watch.navigate(state, "up", view, 10).selected, 0)
        self.assertEqual(watch.navigate(state, "page_down", view, 10).selected, 3)
        self.assertEqual(watch.navigate(state, "left", view, 10).horizontal, 0)
        self.assertEqual(watch.navigate(state, "right", view, 10).horizontal, 12)
        self.assertEqual(watch.navigate(state, "unknown", view, 10), state)

    def test_cfg_call_nodes_keep_callee_names(self):
        value = raw_graph()
        value["functions"][0]["blocks"][0].update(kind="call", calls=["leaf"])
        graph = self.read(value)
        self.assertEqual(graph.function("caller").blocks[0].calls, ("leaf",))
        text = "\n".join(l.text for l in watch.render_graph(watch.View(graph=graph), 160, 40, "cfg", fn="caller"))
        self.assertIn("call leaf", text)

    def test_runtime_rows_merge_with_static_graph_and_live_jobs(self):
        static = self.read(raw_graph())
        inventory = watch_graph.parse_rows({"version": 1, "fn": "caller", "rows": [
            {"name": "finish", "deps": [{"fn": "caller", "name": "local"}]},
            {"name": "local", "deps": [{"fn": "leaf", "name": "call_summary"}]}]})
        graph = watch_graph.merge_runtime(static, inventory, [("caller", "journal_only")], [("new", "active")])
        self.assertEqual(graph.function("caller").blocks, static.function("caller").blocks)
        self.assertEqual(len(static.functions), 3)
        self.assertIsNone(static.function("new"))
        names = {(r.fn, r.name) for r in graph.obligations}
        self.assertEqual(names, {("caller", "finish"), ("caller", "local"), ("leaf", "call_summary"),
                                 ("caller", "journal_only"), ("new", "active")})
        self.assertEqual(graph.function("new").id, "new")
        outline = watch_graph.row_rows(graph, "caller")
        self.assertIn("leaf/call_summary", [r.node for r in outline])

    def test_runtime_row_graph_validates_and_deduplicates_dependencies(self):
        source = {"version": 1, "fn": "caller", "rows": [
            {"name": "one", "deps": [{"fn": "caller", "name": "two"}, {"fn": "caller", "name": "two"}]},
            {"name": "two", "deps": [{"fn": "caller", "name": "one"}]}]}
        graph = watch_graph.merge_runtime(None, watch_graph.parse_rows(source))
        rows = watch_graph.row_rows(graph, "caller")
        self.assertEqual(len(rows), 3)
        self.assertIn("loop", [r.reference for r in rows])
        for value in [None, {}, {"version": True, "fn": "x", "rows": []},
                      {"version": 1, "fn": "x", "rows": [{"name": "", "deps": []}]},
                      {"version": 1, "fn": "x", "rows": [{"name": "a", "deps": [None]}]},
                      {"version": 1, "fn": "x", "rows": [{"name": "a", "deps": []}] * 2}]:
            with self.subTest(value=value), self.assertRaises((ValueError, TypeError, KeyError)):
                watch_graph.parse_rows(value)

    def test_monitor_merges_runtime_inventory_before_any_row_finishes(self):
        self.read(raw_graph())
        directory = self.run / "row-graphs"
        directory.mkdir()
        (directory / "caller.json").write_text(json.dumps({"version": 1, "fn": "caller", "rows": [
            {"name": "regions", "deps": [{"fn": "caller", "name": "region_step_0"}]},
            {"name": "region_step_0", "deps": []}]}))
        (directory / "broken.json").write_text("{")
        before = (directory / "caller.json").read_bytes()
        view = watch.Monitor(self.run, root=self.run).refresh()
        names = [r.node for r in watch.graph_items(view, watch.Navigation(mode="rows", fn="caller"))]
        self.assertEqual(names, ["caller/regions", "caller/region_step_0"])
        text = "\n".join(x.text for x in watch.render_graph(view, 160, 40, "rows", fn="caller"))
        self.assertIn("PROOF DEPENDENCIES", text)
        self.assertIn("region_step_0", text)
        self.assertEqual((directory / "caller.json").read_bytes(), before)

    def test_row_graph_shows_exact_worker_status_and_returns_to_cfg(self):
        inventory = watch_graph.parse_rows({"version": 1, "fn": "caller", "rows": [
            {"name": "step", "deps": []}, {"name": "result", "deps": []}]})
        graph = watch_graph.merge_runtime(self.read(raw_graph()), inventory)
        ask = watch_jobs.Ask(4, "caller", "step", "test", "proof", "cfg", 1)
        row = watch.Row("caller", "result", "closed", "tactics")
        view = watch.View(graph=graph, asks=(ask,), rows={(row.fn, row.name): row})
        text = "\n".join(x.text for x in watch.render_graph(view, 160, 40, "rows", fn="caller"))
        self.assertIn("[*] caller/step", text)
        self.assertIn("[+] caller/result", text)
        state = watch.Navigation(mode="functions")
        state = watch.navigate(state, "rows", view, 10)
        self.assertEqual((state.mode, state.fn), ("rows", "caller"))
        cfg = watch.navigate(state, "enter", view, 10)
        self.assertEqual((cfg.mode, cfg.fn), ("cfg", "caller"))


if __name__ == "__main__": unittest.main()
