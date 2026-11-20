"""Lean lexical masking for source audits; comments/literals are not proof tokens."""
import re

class AuditError(ValueError):
    pass

def require(condition, message):
    if not condition:
        raise AuditError(message)

def lean_code_mask(text: str) -> str:
    """Hide nested comments and string/character literals, retaining line breaks.

    This is lexical filtering, not elaboration. Interpolation expressions are
    preserved as code, so a proof term inside a string interpolation is audited.
    """
    result = list(text)
    interpolations = []
    size = len(text)

    def hide(start, end):
        for k in range(start, end):
            if text[k] not in "\r\n":
                result[k] = " "

    def block(start):
        depth, k = 1, start + 2
        while k < size and depth:
            if text.startswith("/-", k):
                depth += 1
                k += 2
            elif text.startswith("-/", k):
                depth -= 1
                k += 2
            else:
                k += 1
        require(depth == 0, "unterminated Lean block comment")
        return k

    def char(start):
        # Identifier primes are not character literals.
        if start and (text[start - 1].isalnum() or text[start - 1] in "_'Ãƒâ€šÃ‚Â»"):
            return None
        k = start + 1
        while k < size and text[k] not in "\r\n":
            if text[k] == "\\":
                k += 2
            elif text[k] == "'":
                return k + 1
            else:
                k += 1
        return None

    def literal(start):
        raw = re.match(r'r(#+)?"', text[start:])
        if raw and (not start or not (text[start - 1].isalnum() or text[start - 1] in "_'")):
            tag = '"' + (raw[1] or "")
            end = text.find(tag, start + len(raw[0]))
            require(end >= 0, "unterminated Lean raw string")
            return end + len(tag)
        if text[start] != '"':
            return None
        interpolated = start >= 2 and text[start - 2:start] in {"s!", "m!", "f!"}
        k = start + 1
        while k < size:
            if text[k] == "\\":
                k += 2
            elif text[k] == '"':
                return k + 1
            elif interpolated and text[k] == "{":
                if text.startswith("{{", k):
                    k += 2
                    continue
                depth = 1
                k += 1
                expression_start = k
                while k < size and depth:
                    if text.startswith("/-", k):
                        k = block(k)
                    elif text.startswith("--", k):
                        while k < size and text[k] not in "\r\n":
                            k += 1
                    elif text[k] == '"' or text[k] == "r" and re.match(r'r(#+)?"', text[k:]):
                        end = literal(k)
                        k = end if end is not None else k + 1
                    elif text[k] == "'" and (end := char(k)) is not None:
                        k = end
                    else:
                        if text[k] == "{":
                            depth += 1
                        elif text[k] == "}":
                            depth -= 1
                        k += 1
                require(depth == 0, "unterminated Lean string interpolation")
                interpolations.append((expression_start, k - 1))
            else:
                k += 1
        raise AuditError("unterminated Lean string")

    k = 0
    while k < size:
        if text.startswith("/-", k):
            end = block(k)
        elif text.startswith("--", k):
            end = k
            while end < size and text[end] not in "\r\n":
                end += 1
        elif text[k] == '"' or text[k] == "r" and re.match(r'r(#+)?"', text[k:]):
            end = literal(k)
            if end is None:
                k += 1
                continue
        elif text[k] == "'" and (end := char(k)) is not None:
            pass
        else:
            k += 1
            continue
        hide(k, end)
        k = end
    for start, end in sorted(interpolations, key=lambda pair: pair[1] - pair[0], reverse=True):
        result[start:end] = lean_code_mask(text[start:end])
    return "".join(result)



MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")

def lean_header_imports(text: str) -> list[str]:
    masked = lean_code_mask(text)
    imports = []
    pending, previous_import = False, False
    boundaries = {"namespace", "section", "end", "open", "variable", "universe", "set_option",
                  "def", "abbrev", "theorem", "lemma", "instance", "structure", "class", "inductive",
                  "axiom", "opaque", "example", "noncomputable", "private", "protected", "public",
                  "unsafe", "partial", "mutual", "attribute", "syntax", "macro", "macro_rules", "elab",
                  "elab_rules", "infix", "infixl", "infixr", "notation", "export", "initialize"}
    for line in masked.splitlines():
        # Lean's quoted ASCII identifiers name the same module components.
        # Normalize those components before matching the import header.
        line = re.sub(r"«([A-Za-z_][A-Za-z0-9_']*)»", r"\1", line)
        stripped = line.strip()
        if not stripped:
            continue
        if stripped in {"module", "prelude"}:
            require(not pending, "missing Lean import module")
            previous_import = False
            continue
        match = re.match(r"^(?:public\s+|private\s+)?import(?:\s+(.*)|$)", stripped)
        if match:
            require(not pending, "missing Lean import module")
            names = (match[1] or "").split()
            pending = not names
        elif pending or previous_import and line[0].isspace() and stripped.split()[0] not in boundaries:
            names = stripped.split()
            if not pending and any(not MODULE_NAME.fullmatch(n) for n in names):
                break
            pending = False
        else:
            break  # Lean body commands are outside the import header.
        for name in names:
            require(bool(MODULE_NAME.fullmatch(name)) and name not in boundaries, f"invalid import module: {name!r}")
        imports.extend(names)
        previous_import = True
    require(not pending, "missing Lean import module")
    return imports

