"""Audit byte-value dependence in the pinned Config A Python script builder.

This is a source-shape check plus a pinned source digest. It is not a formal
semantics proof for Python, the compiled interpreter, or all builder inputs.
"""

import argparse
import ast
import hashlib
import json
from pathlib import Path


PINNED_SHA256 = "c7e52af90bd0d9fce9834fce26dcd67aee0d7751ee228d9730873c4d12659a5c"


def function(nodes, name):
    matches = [n for n in nodes if isinstance(n, ast.FunctionDef) and n.name == name]
    assert len(matches) == 1, name
    return matches[0]


def calls(tree, name):
    return [
        node for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == name
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    source_path = args.app_root.resolve() / "worker/cpu/bitcoin_tx.py"
    source = source_path.read_bytes()
    source_hash = hashlib.sha256(source).hexdigest()
    assert source_hash == PINNED_SHA256, "Builder source changed; re-audit required"
    tree = ast.parse(source)
    builder = next(
        n for n in tree.body
        if isinstance(n, ast.ClassDef) and n.name == "QSBScriptBuilder"
    )
    model = next(
        n for n in tree.body
        if isinstance(n, ast.ClassDef) and n.name == "_StackModel"
    )
    emit = function(builder.body, "_emit_round")
    build = function(builder.body, "build_full_script")
    pinning = function(builder.body, "build_pinning_script")
    canonical = function(builder.body, "_canonical_subset")
    push = function(tree.body, "push_data")

    # The only reads of variable commitment/dummy/nonce bytes in _emit_round
    # are the three data pushes. Output bytes are never read back into the
    # token model or an opcode-depth calculation.
    push_calls = sorted(calls(emit, "push_data"), key=lambda n: n.lineno)
    push_inputs = [ast.unparse(n.args[0]) for n in push_calls]
    assert push_inputs == [
        "self.hors_commitments[R][p]",
        "self.dummy_sigs[R][p]",
        "sig_nonce_bytes",
    ]
    byte_attr_loads = [
        (n.attr, n.lineno) for n in ast.walk(emit)
        if isinstance(n, ast.Attribute)
        and n.attr in {"hors_commitments", "dummy_sigs"}
    ]
    assert sorted(byte_attr_loads) == sorted(
        [("hors_commitments", push_calls[0].lineno),
         ("dummy_sigs", push_calls[1].lineno)]
    )
    nonce_loads = [
        n.lineno for n in ast.walk(emit)
        if isinstance(n, ast.Name) and n.id == "sig_nonce_bytes"
        and isinstance(n.ctx, ast.Load)
    ]
    assert nonce_loads == [push_calls[2].lineno]
    out_reads = [
        n.lineno for n in ast.walk(emit)
        if isinstance(n, ast.Name) and n.id == "out"
        and isinstance(n.ctx, ast.Load)
    ]
    return_line = next(
        n.lineno for n in emit.body if isinstance(n, ast.Return)
    )
    assert out_reads == [return_line]
    for call in ast.walk(emit):
        if not isinstance(call, ast.Call):
            continue
        if not isinstance(call.func, ast.Attribute):
            continue
        if not isinstance(call.func.value, ast.Name) or call.func.value.id != "m":
            continue
        assert call.func.attr in {"push", "pop", "roll", "depth", "deepest_dummy"}
        args_text = " ".join(ast.unparse(arg) for arg in call.args)
        assert not any(
            tainted in args_text
            for tainted in ("sig_nonce_bytes", "hors_commitments", "dummy_sigs", "out")
        )
    assert all(
        not any(
            isinstance(child, ast.Name) and child.id in {"sig_nonce_bytes", "out"}
            or isinstance(child, ast.Attribute)
            and child.attr in {"hors_commitments", "dummy_sigs"}
            for child in ast.walk(test.test)
        )
        for test in ast.walk(emit)
        if isinstance(test, (ast.If, ast.While))
    )

    # The data serializer's branch conditions depend on len(data), never on
    # payload bytes. All Config A commitments/dummies and a short DER nonce
    # therefore use a direct push. The source hash fixes the return bodies.
    assert ast.unparse(push.body[1]) == "n = len(data)"
    assert all(
        {n.id for n in ast.walk(test.test) if isinstance(n, ast.Name)} <= {"n"}
        for test in ast.walk(push)
        if isinstance(test, ast.If)
    )
    assert ast.unparse(canonical.body[-1]) == "return list(range(t_total))"
    pin_pushes = calls(pinning, "push_data")
    assert len(pin_pushes) == 1
    assert ast.unparse(pin_pushes[0].args[0]) == "sig_nonce_bytes"
    assert [
        n.lineno for n in ast.walk(pinning)
        if isinstance(n, ast.Name) and n.id == "sig_nonce_bytes"
        and isinstance(n.ctx, ast.Load)
    ] == [pin_pushes[0].lineno]
    assert all(
        not any(isinstance(n, ast.Name) and n.id == "sig_nonce_bytes"
                for n in ast.walk(test.test))
        for test in ast.walk(pinning) if isinstance(test, ast.If)
    )
    single_hash_branch = next(n for n in build.body if isinstance(n, ast.If))
    assert ast.unparse(single_hash_branch.test) == (
        "self.hash_mode in ('ripemd160', 'sha256')"
    )
    assert ast.unparse(single_hash_branch.body[-1]) == "return bytes(script) + s0 + s1"
    emit_calls = [
        ast.unparse(n) for n in ast.walk(single_hash_branch)
        if isinstance(n, ast.Call)
        and isinstance(n.func, ast.Attribute)
        and n.func.attr == "_emit_round"
    ]
    assert emit_calls == [
        "self._emit_round(m, 0, round1_sig, self._canonical_subset(0))",
        "self._emit_round(m, 1, round2_sig, self._canonical_subset(1))",
    ]
    assert [
        ast.unparse(n) for n in ast.walk(single_hash_branch)
        if isinstance(n, ast.Call)
        and isinstance(n.func, ast.Attribute)
        and n.func.attr == "build_pinning_script"
    ] == ["self.build_pinning_script(pin_sig)"]
    for name in ("pin_sig", "round1_sig", "round2_sig"):
        assert len([
            n for n in ast.walk(single_hash_branch)
            if isinstance(n, ast.Name) and n.id == name
            and isinstance(n.ctx, ast.Load)
        ]) == 1
    assert all(
        not isinstance(n, ast.Attribute)
        or n.attr not in {"hors_commitments", "dummy_sigs"}
        for method in model.body if isinstance(method, ast.FunctionDef)
        for n in ast.walk(method)
    )

    report = {
        "builder_sha256": source_hash,
        "emit_round_data_push_inputs": push_inputs,
        "emit_round_out_read_lines": out_reads,
        "byte_values_only_enter_emit_round_push_data": True,
        "stack_model_calls_have_no_byte_value_arguments": True,
        "push_data_conditions_use_only_length": True,
        "canonical_subset_uses_round_total": True,
        "pin_signature_only_enters_pinning_push_data": True,
        "full_builder_signatures_only_enter_expected_calls": True,
        "scope": (
            "Pinned Python AST source-shape audit; supports value-independent "
            "opcode suffix under fixed Config A parameters and short push lengths. "
            "Not a formal Python/Core refinement or a quantum spend bound."
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("Audited pinned builder data-flow shape.")


if __name__ == "__main__":
    main()
