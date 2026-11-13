"""Download the pinned CPU compiler/header wheels into a fresh local directory.

No package is installed, no Python from the wheels is imported, and no CUDA
driver or GPU is used. Downloads use verified TLS and fixed wheel SHA-256 pins.
"""

import argparse
import json
from pathlib import Path, PurePosixPath
import platform
import sys
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from reproduction.ptx.compile_full_shape import WHEELS, digest, require, write  # noqa: E402


def fetch(output):
    output = output.resolve()
    require(platform.system() == "Linux" and platform.machine() == "x86_64",
            "These pinned wheels target Linux x86_64")
    require(not output.exists() and not any((p / ".git").exists()
            for p in (output, *output.parents)), "Fresh compiler directory outside Git required")
    output.mkdir(parents=True)
    rows = []
    for package, (version, expected) in WHEELS.items():
        row = {"package": package, "version": version, "status": "started"}
        rows.append(row)
        write(output / "downloads.json", rows)
        try:
            url = f"https://pypi.org/pypi/{package}/{version}/json"
            with urllib.request.urlopen(url, timeout=30) as response:
                metadata = response.read()
            (output / (package + "-metadata.json")).write_bytes(metadata)
            choices = [item for item in json.loads(metadata)["urls"]
                       if item["filename"].endswith(".whl") and "manylinux" in item["filename"]
                       and "x86_64" in item["filename"]]
            require(len(choices) == 1 and choices[0]["digests"]["sha256"] == expected,
                    "Exactly the pinned Linux compiler wheel is required")
            wheel = choices[0]
            require(Path(wheel["filename"]).name == wheel["filename"]
                    and wheel["url"].startswith("https://files.pythonhosted.org/"),
                    "Unexpected package download location")
            with urllib.request.urlopen(wheel["url"], timeout=30) as response:
                content = response.read()
            require(digest(content) == expected, "Downloaded compiler wheel differs")
            destination = output / wheel["filename"]
            destination.write_bytes(content)
            with zipfile.ZipFile(destination) as archive:
                require(all(not PurePosixPath(name).is_absolute()
                            and ".." not in PurePosixPath(name).parts for name in archive.namelist()),
                        "Unsafe wheel paths")
                archive.extractall(output / "packages")
            row.update(status="downloaded-and-hash-verified", filename=wheel["filename"],
                       url=wheel["url"], sha256=expected, bytes=len(content), metadata_url=url,
                       metadata_sha256=digest(metadata), tls_verification=True)
        except Exception as error:
            row.update(status="failed", error=repr(error))
            write(output / "downloads.json", rows)
            raise
        write(output / "downloads.json", rows)
        print(json.dumps({"package": package, "version": version, "sha256": expected}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    fetch(parser.parse_args().output)


if __name__ == "__main__":
    main()
