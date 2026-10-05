#!/usr/bin/env python3
"""Check source requirements before builds; full Palomar verification is still required.

Scanner functions follow PalomarSubmission/scripts/source_requirements.py.
"""
import os
import re
import json
from pathlib import Path

COMMENT_MARKER = re.compile(r"/-|-/")
# Lean 4 Init/Meta/Defs.lean identifier characters; Python Unicode classes
# are broader. A qualified identifier also continues across a dot.
ID_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}«]")


def has_module_header(text: str) -> bool:
    """Recognize the initial marker, without confusing comments with headers.

    Documentation comments are commands, not header whitespace. Do not strip a
    BOM or arbitrary Unicode whitespace: Lean's header parser does not either.
    This cheap check precedes installation; execute confirms with --deps-json.
    """
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            # Lean consumes the character after the plain opener before
            # scanning its body (unlike nested openers). Match its parser.
            index += 3
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    break
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
            if depth:
                return False
        else:
            return text.startswith("module", index) and (
                IDENTIFIER_CONTINUATION.match(text, index + 6) is None
            )
    return False


def physical_lines(text: str) -> int:
    """LF/CRLF lines; an unterminated final line counts, a final LF adds none."""
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def lean_source_files(root: Path) -> list[Path]:
    """Lean source paths, including contained projects and symlinks to reject.

    Lake configuration shares the line cap, but is exempt from module headers.
    Never traverse symlinks or Git internals.
    """
    files = []
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(
            name for name in subdirectories
            if name not in {".git", ".lake"} and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            path = Path(directory) / name
            if name.endswith(".lean") and (path.is_symlink() or path.is_file()):
                files.append(path)
    return files


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failed = False
    try:
        config = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
        challenge = config["challenge_module"]
        if not isinstance(challenge, str) or not re.fullmatch(
            r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", challenge
        ):
            raise ValueError("challenge_module is not a safe dotted module name")
        challenge_path = root / (challenge.replace(".", "/") + ".lean")
        if not challenge_path.is_file() or challenge_path.is_symlink():
            raise ValueError("Challenge must be a regular source file inside this project")
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as error:
        print(f"comparator.json: cannot identify the allowed Challenge holes: {error}")
        return 1
    for path in lean_source_files(root):
        relative = path.relative_to(root)
        if path.is_symlink():
            print(f"{relative}: must be a regular Lean file, not a symbolic link")
            failed = True
            continue
        try:
            text = path.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            print(f"{relative}: source is not valid UTF-8")
            failed = True
            continue
        if path.name != "lakefile.lean" and not has_module_header(text):
            print(f"{relative}: must use the module header keyword")
            failed = True
        if physical_lines(text) > 10_000:
            print(f"{relative}: exceeds 10,000 lines; split into smaller modules")
            failed = True
        if path == challenge_path:
            if physical_lines(text) > 1_000 or len(text.encode("utf-8")) > 100 * 1024:
                print(f"{relative}: Challenge exceeds 1,000 lines or 100 KiB")
                failed = True
            continue
        # This conservative source check catches ordinary unfinished proofs before
        # compilation. Kernel replay and transitive axiom checking remain the
        # responsibility of Comparator and the complete Palomar workflow.
        for token, line in source_identifiers(text):
            if token in {"sorry", "admit", "sorryAx", "axiom", "native_decide",
                         "ofReduceBool", "implemented_by"}:
                print(f"{relative}:{line}: forbidden proof construct {token!r}")
                failed = True
    return int(failed)


def source_identifiers(text: str):
    """Yield identifiers outside comments and strings, preserving line numbers.

    This is a source-hygiene scanner, not Lean's parser or an axiom checker.
    Nested block comments and escaped strings are skipped. Quoted identifiers
    are kept so quoted spellings cannot conceal an unfinished proof token.
    """
    index = 0
    line = 1
    while index < len(text):
        if text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end
        elif text.startswith("/-", index):
            depth = 1
            index += 2
            while index < len(text) and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    line += int(text[index] == "\n")
                    index += 1
        elif text[index] == '"':
            index += 1
            while index < len(text):
                character = text[index]
                line += int(character == "\n")
                index += 1
                if character == "\\" and index < len(text):
                    line += int(text[index] == "\n")
                    index += 1
                elif character == '"':
                    break
        elif text[index] == "«":
            start_line = line
            end = text.find("»", index + 1)
            if end < 0:
                end = len(text)
            token = text[index + 1:end]
            line += token.count("\n")
            yield token, start_line
            index = end + 1
        elif text[index].isalpha() or text[index] == "_":
            start = index
            index += 1
            while index < len(text) and (text[index].isalnum() or text[index] in "_'?!"):
                index += 1
            yield text[start:index], line
        else:
            line += int(text[index] == "\n")
            index += 1


if __name__ == "__main__":
    raise SystemExit(main())
