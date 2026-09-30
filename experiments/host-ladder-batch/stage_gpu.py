"""Render the isolated host-ladder GPU handoff; reuse bounded table-only ZIP transport."""
import argparse
import hashlib
import inspect
import io
import os
from pathlib import Path, PurePosixPath
import re
import shlex
import stat
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
MAX_ARCHIVE = 10_000_000
MAX_MEMBER = 10_000_000
MAX_TOTAL = 50_000_000
MAX_SOURCE = 256_000
# Transport intentionally matches exact-table-batch/stage.py; only host binding differs.
SOURCES = {"host.sh": "experiments/host-ladder-batch/host-gpu.sh",
           "ready.sh": "ops/aws-gpu-execution/ready.sh"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def valid_hash(value):
    require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value), "SHA256 required")


def validate_archive(archive, zip_sha256, binary_sha256):
    """Return only the verified root table-gate bytes; never execute or extract others."""
    valid_hash(zip_sha256)
    valid_hash(binary_sha256)
    if isinstance(archive, bytes):
        raw = archive
    else:
        with Path(archive).open("rb") as stream:
            raw = stream.read(MAX_ARCHIVE + 1)
    require(len(raw) <= MAX_ARCHIVE, "archive too large")
    require(hashlib.sha256(raw).hexdigest() == zip_sha256, "archive SHA256 mismatch")
    with zipfile.ZipFile(io.BytesIO(raw)) as bundle:
        infos = bundle.infolist()
        require(len(infos) <= 1000, "too many archive members")
        names = [info.filename for info in infos]
        require(len(names) == len(set(names)), "duplicate archive member")
        require(sum(info.file_size for info in infos) <= MAX_TOTAL, "expanded archive too large")
        for info in infos:
            name = info.filename
            parts = name.rstrip("/").split("/")
            require(name == info.orig_filename and name and "\\" not in name and
                    not PurePosixPath(name).is_absolute() and
                    all(part not in ("", ".", "..") for part in parts), "unsafe archive member")
            mode = stat.S_IFMT(info.external_attr >> 16)
            require(mode in (0, stat.S_IFREG, stat.S_IFDIR) and
                    (mode != stat.S_IFDIR or info.is_dir()) and
                    (mode != stat.S_IFREG or not info.is_dir()), "nonregular archive member")
            require(not info.flag_bits & 1, "encrypted archive member")
            require(info.compress_type in (zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED), "unsupported compression")
            require(0 <= info.file_size <= MAX_MEMBER, "archive member too large")
        require("table-gate" in names, "missing exact table-gate entry")
        info = bundle.getinfo("table-gate")
        require(not info.is_dir(), "table-gate must be regular")
        with bundle.open(info) as stream:
            binary = stream.read(MAX_MEMBER + 1)
        require(0 < len(binary) <= MAX_MEMBER and len(binary) == info.file_size, "invalid binary size")
        require(hashlib.sha256(binary).hexdigest() == binary_sha256, "table-gate SHA256 mismatch")
        return binary


def extract_table_gate(archive, output, zip_sha256, binary_sha256):
    binary = validate_archive(archive, zip_sha256, binary_sha256)
    with Path(output).open("xb") as stream:
        stream.write(binary)
        os.fchmod(stream.fileno(), 0o755)


def download(url, limit, seconds):
    """Bound curl's wall time and bytes read, including servers without Content-Length."""
    command = ["curl", "--fail", "--silent", "--show-error", "--location",
               "--proto", "=https", "--proto-redir", "=https", "--max-time", str(seconds),
               "--max-filesize", str(limit), url]
    with subprocess.Popen(command, stdout=subprocess.PIPE) as process:
        try:
            raw = process.stdout.read(limit + 1)
            require(len(raw) <= limit, "download too large")
            require(process.wait(timeout=5) == 0, "download failed")
            return raw
        finally:
            if process.poll() is None:
                process.kill()
            process.wait()


def payload(commit):
    require(re.fullmatch(r"[0-9a-f]{40}", commit), "full committed SHA required")
    require(subprocess.check_output(["git", "cat-file", "-t", commit], cwd=ROOT,
                                    timeout=30).strip() == b"commit", "commit object required")
    result = {}
    for name, source in SOURCES.items():
        raw = subprocess.check_output(["git", "show", commit + ":" + source], cwd=ROOT, timeout=30)
        require(0 < len(raw) <= MAX_SOURCE, "committed source too large or empty")
        result[name] = {"sha256": hashlib.sha256(raw).hexdigest(),
                        "url": "https://raw.githubusercontent.com/starknet-innovation/qsb-solver/" + commit + "/" + source}
    return result


def render(commit, url, zip_sha256, binary_sha256, image):
    valid_hash(zip_sha256)
    valid_hash(binary_sha256)
    require(re.fullmatch(r"https://[^\s]+", url) and "\x00" not in url, "HTTPS artifact URL required")
    require(re.fullmatch(r"ghcr\.io/starknet-innovation/qsb-solver@sha256:[0-9a-f]{64}", image), "immutable runtime required")
    sources = payload(commit)
    script = "set -euo pipefail\nDEADLINE=__DEADLINE__\n[[ \"$DEADLINE\" =~ ^[0-9]{10}$ ]]\n"
    # The outer cap covers all transport and extraction, not just one HTTP request.
    script += "timeout --signal=TERM --kill-after=5s 180 python3 - <<'QSB_TABLE_STAGE'\n"
    script += "import hashlib,io,os,re,stat,subprocess,zipfile\nfrom pathlib import Path,PurePosixPath\n"
    script += f"MAX_ARCHIVE={MAX_ARCHIVE}\nMAX_MEMBER={MAX_MEMBER}\nMAX_TOTAL={MAX_TOTAL}\n"
    for function in (require, valid_hash, validate_archive, extract_table_gate, download):
        script += inspect.getsource(function) + "\n"
    script += "root=Path('/opt/qsb-a10g-gate'); root.mkdir()\n"
    script += f"archive=download({url!r},MAX_ARCHIVE,120)\n"
    script += f"extract_table_gate(archive,root/'table-gate',{zip_sha256!r},{binary_sha256!r})\n"
    script += f"sources={sources!r}\n"
    script += "for name,item in sources.items():\n"
    script += f" raw=download(item['url'],{MAX_SOURCE},30)\n"
    script += " require(hashlib.sha256(raw).hexdigest()==item['sha256'],'committed source SHA256 mismatch')\n"
    script += " with (root/name).open('xb') as stream: stream.write(raw)\n"
    script += "with (root/'SHA256SUMS').open('x') as stream:\n"
    script += " for name in ('host.sh','ready.sh','table-gate'):\n"
    script += "  stream.write(hashlib.sha256((root/name).read_bytes()).hexdigest()+'  '+name+'\\n')\n"
    script += "QSB_TABLE_STAGE\n"
    script += 'timeout --signal=TERM --kill-after=5s 190 bash /opt/qsb-a10g-gate/ready.sh "$DEADLINE"\n'
    script += 'bash /opt/qsb-a10g-gate/host.sh ' + shlex.quote(image) + ' "$DEADLINE"\n'
    require(len(script.encode()) <= 60000, "SSM handoff too large")
    return script


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    generate = commands.add_parser("render")
    generate.add_argument("--commit", required=True)
    generate.add_argument("--artifact-url-file", type=Path, required=True)
    generate.add_argument("--image", required=True)
    generate.add_argument("--output", type=Path, required=True)
    check = commands.add_parser("check-archive")
    check.add_argument("archive", type=Path)
    check.add_argument("--output", type=Path, help="optional exclusive table-gate extraction")
    for command in (generate, check):
        command.add_argument("--zip-sha256", required=True)
        command.add_argument("--binary-sha256", required=True)
    args = parser.parse_args()
    if args.command == "render":
        script = render(args.commit, args.artifact_url_file.read_text().strip(),
                        args.zip_sha256, args.binary_sha256, args.image)
        with args.output.open("x") as stream:
            stream.write(script)
    elif args.output:
        extract_table_gate(args.archive, args.output, args.zip_sha256, args.binary_sha256)
        print("Verified and extracted table-gate; no execution performed.")
    else:
        binary = validate_archive(args.archive, args.zip_sha256, args.binary_sha256)
        print(f"Verified table-gate: {len(binary)} bytes, SHA256 {args.binary_sha256}; no execution performed.")


if __name__ == "__main__":
    main()
