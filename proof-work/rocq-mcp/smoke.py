"""Exercise the installed server over MCP stdio, then independently kernel-check.

Run with .rocq-mcp-local/venv/bin/python proof-work/rocq-mcp/smoke.py.
Only the launcher's isolated external workspace is written.
"""
import asyncio
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

from fastmcp import Client
from fastmcp.client.transports import StdioTransport

ROOT = Path(__file__).resolve().parents[2]
RUNTIME = ROOT / ".rocq-mcp-local"


async def main():
    rows = []
    workspace = Path(tempfile.mkdtemp(prefix="simplicity-rocq-mcp-smoke.", dir="/private/tmp"))
    transport = StdioTransport(
        command="/bin/bash",
        args=[str(ROOT / "proof-work/rocq-mcp/launch.sh")],
        cwd=str(ROOT),
        env={**os.environ, "SIMPLICITY_ROCQ_WORKSPACE": str(workspace)},
        log_file=RUNTIME / "smoke-stderr.log",
    )
    async with Client(transport, timeout=45) as client:
        async def call(name, args):
            result = await client.call_tool(name, args, raise_on_error=False)
            data = result.data
            rows.append({"tool": name, "args": args, "result": data})
            print(name, json.dumps(data, default=str)[:1800], flush=True)
            (RUNTIME / "smoke.json").write_text(json.dumps(rows, indent=2, default=str))
            return data

        health = await call("rocq_health", {})
        assert health["success"] and health["ok"], health
        assert health["toolchain"]["coqc"]["version"] == "8.17.1 4.14.1", health
        assert Path(health["toolchain"]["coqc"]["path"]) == RUNTIME / "backend/bin/coqc", health
        assert Path(health["toolchain"]["pet"]["path"]) == RUNTIME / "bin/pet", health
        assert health["toolchain"]["pet"]["version"] == "0.2.4-dev", health
        await call("rocq_diag", {})
        assert workspace.is_relative_to(Path("/private/tmp")), workspace
        source = workspace / "FrameProbe.v"
        def lemma(text):
            return text.split("Lemma eval_frame_edge_ofs_early", 1)[1].split("Qed.", 1)[0]
        assert lemma(source.read_text()) == lemma((ROOT / "Coq/C/jet_read8.v").read_text())
        proof = source.read_text().split("Proof.", 1)[1].split("Qed.", 1)[0]
        start = await call("rocq_start", {
            "file": str(source), "theorem": "eval_frame_edge_ofs_early",
            "workspace": str(workspace), "timeout": 20,
        })
        assert start["success"], start
        intro, rest = proof.strip().split("\n", 1)
        state = await call("rocq_check", {
            "body": intro, "from_state": start["state_id"], "timeout": 10,
        })
        assert state["success"], state
        bad = await call("rocq_check", {
            "body": "apply eval_Etempvar.", "from_state": state["state_id"],
            "timeout": 10,
        })
        assert bad["success"] is False, bad
        assert bad["reason"] == "tactic_failed", bad
        assert bad["last_valid_state_id"] == state["state_id"], bad
        query = await call("rocq_query", {
            "command": "Check eval_Efield_struct.",
            "from_state": state["state_id"], "timeout": 10,
        })
        assert query["success"], query
        done = await call("rocq_check", {
            "body": rest + "\nQed.", "from_state": state["state_id"],
            "timeout": 20,
        })
        assert done["success"] and done["proof_finished"], done
        compiled = await call("rocq_compile_file", {
            "file": str(source), "workspace": str(workspace),
            "mode": "full", "keep_vo": True, "timeout": 30,
        })
        assert compiled["success"], compiled

    flags = shlex.split((workspace / "_CoqProject").read_text())
    env = os.environ.copy()
    env.update({
        "COQLIB": str(RUNTIME / "backend/lib/coq"),
        "COQCORELIB": str(RUNTIME / "backend/lib/coq-core"),
        "OCAMLPATH": str(RUNTIME / "backend/lib"),
        "CAML_LD_LIBRARY_PATH": str(RUNTIME / "backend/lib/stublibs") + ":" +
            str(RUNTIME / "backend/lib/ocaml/stublibs"),
    })
    command = [str(RUNTIME / "backend/bin/coqchk"), "-silent", "-o", *flags, "FrameProbe"]
    checked = subprocess.run(command, cwd=workspace, env=env, text=True,
                             capture_output=True, timeout=120)
    rows.append({"command": command, "exit": checked.returncode,
                 "stdout": checked.stdout, "stderr": checked.stderr})
    rows.append({"sha256": {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in [ROOT / "proof-work/rocq-mcp/launch.sh",
                     ROOT / "proof-work/rocq-mcp/smoke.py",
                     ROOT / "Coq/C/jet_read8.v", RUNTIME / "bin/pet",
                     RUNTIME / "workspace-template/FrameProbe.v"]
    }})
    (RUNTIME / "smoke.json").write_text(json.dumps(rows, indent=2, default=str))
    assert checked.returncode == 0, checked.stderr
    print("Independent recursive coqchk passed; workspace:", workspace, flush=True)


if __name__ == "__main__":
    asyncio.run(main())
