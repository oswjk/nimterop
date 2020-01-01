import dynlib, macros, os, sequtils, sets, strformat, strutils, tables, times

import regex

import compiler/[ast, idents, lineinfos, msgs, pathutils, renderer]

import "."/[build, compat, globals, plugin, treesitter/api]

const gReserved = """
addr and as asm
bind block break
case cast concept const continue converter
defer discard distinct div do
elif else end enum except export
finally for from func
if import in include interface is isnot iterator
let
macro method mixin mod
nil not notin
of or out
proc ptr
raise ref return
shl shr static
template try tuple type
using
var
when while
xor
yield""".split(Whitespace).toHashSet()

# Types related

const gTypeMap* = {
  # char
  "char": "cchar",
  "signed char": "cschar",
  "unsigned char": "cuchar",

  # short
  "short": "cshort",
  "short int": "cshort",
  "signed short": "cshort",
  "signed short int": "cshort",
  "unsigned short": "cushort",
  "unsigned short int": "cushort",
  "uShort": "cushort",
  "u_short": "cushort",

  # int
  "int": "cint",
  "signed": "cint",
  "signed int": "cint",
  "ssize_t": "int",
  "unsigned": "cuint",
  "unsigned int": "cuint",
  "uInt": "cuint",
  "u_int": "cuint",
  "size_t": "uint",

  # long
  "long": "clong",
  "long int": "clong",
  "signed long": "clong",
  "signed long int": "clong",
  "off_t": "clong",
  "unsigned long": "culong",
  "unsigned long int": "culong",
  "uLong": "culong",
  "u_long": "culong",

  # long long
  "long long": "clonglong",
  "long long int": "clonglong",
  "signed long long": "clonglong",
  "signed long long int": "clonglong",
  "off64_t": "clonglong",
  "unsigned long long": "culonglong",
  "unsigned long long int": "culonglong",

  # floating point
  "float": "cfloat",
  "double": "cdouble",
  "long double": "clongdouble"
}.toTable()

proc getType*(str: string): string =
  if str == "void":
    return "object"

  result = str.strip(chars={'_'}).
    replace(re"\s+", " ").
    replace(re"^([u]?int[\d]+)_t$", "$1").
    replace(re"^([u]?int)ptr_t$", "ptr $1")

  if gTypeMap.hasKey(result):
    result = gTypeMap[result]

proc getPtrType*(str: string): string =
  result = case str:
    of "ptr cchar":
      "cstring"
    of "ptr ptr cchar":
      "ptr cstring"
    of "ptr object":
      "pointer"
    of "ptr ptr object":
      "ptr pointer"
    else:
      str

# Identifier related

proc checkIdentifier(name, kind, parent, origName: string) =
  let
    parentStr = if parent.nBl: parent & ":" else: ""

  if name.nBl:
    let
      origStr = if name != origName: &", originally '{origName}' before 'cPlugin:onSymbol()', still" else: ""
      errmsg = &"Identifier '{parentStr}{name}' ({kind}){origStr} contains"

    doAssert name[0] != '_' and name[^1] != '_', errmsg & " leading/trailing underscores '_'"

    doAssert (not name.contains("__")): errmsg & " consecutive underscores '_'"

  if parent.nBl:
    doAssert name.nBl, &"Blank identifier, originally '{parentStr}{origName}' ({kind}), cannot be empty"

proc getIdentifier*(nimState: NimState, name: string, kind: NimSymKind, parent=""): string =
  doAssert name.nBl, "Blank identifier error"

  if name notin nimState.gState.symOverride or parent.nBl:
    if nimState.gState.onSymbol != nil:
      # Use onSymbol from plugin provided by user
      var
        sym = Symbol(name: name, parent: parent, kind: kind)
      nimState.gState.onSymbol(sym)

      result = sym.name
    else:
      result = name

      # Strip out --prefix from CLI if specified
      for str in nimState.gState.prefix:
        if result.startsWith(str):
          result = result[str.len .. ^1]

      # Strip out --suffix from CLI if specified
      for str in nimState.gState.suffix:
        if result.endsWith(str):
          result = result[0 .. ^(str.len+1)]

    checkIdentifier(result, $kind, parent, name)

    if result in gReserved or (result == "object" and kind != nskType):
      # Enclose in backticks since Nim reserved word
      result = &"`{result}`"
  else:
    # Skip identifier since in symOverride
    result = ""

proc getUniqueIdentifier*(nimState: NimState, prefix = ""): string =
  var
    name = prefix & "_" & nimState.sourceFile.extractFilename().multiReplace([(".", ""), ("-", "")])
    nimName = name[0] & name[1 .. ^1].replace("_", "").toLowerAscii
    count = 1

  while (nimName & $count) in nimState.identifiers:
    count += 1

  return name & $count

proc addNewIdentifer*(nimState: NimState, name: string, override = false): bool =
  if override or name notin nimState.gState.symOverride:
    let
      nimName = name[0] & name[1 .. ^1].replace("_", "").toLowerAscii

    if nimState.identifiers.hasKey(nimName):
      doAssert name == nimState.identifiers[nimName],
        &"Identifier '{name}' is a stylistic duplicate of identifier " &
        &"'{nimState.identifiers[nimName]}', use 'cPlugin:onSymbol()' to rename"
      result = false
    else:
      nimState.identifiers[nimName] = name
      result = true

# Overrides related

proc getOverride*(nimState: NimState, name: string, kind: NimSymKind): string =
  doAssert name.nBl, "Blank identifier error"

  if nimState.gState.onSymbolOverride != nil:
    var
      nname = nimState.getIdentifier(name, kind, "Override")
      sym = Symbol(name: nname, kind: kind)
    if nname.nBl:
      nimState.gState.onSymbolOverride(sym)

      if sym.override.nBl and nimState.addNewIdentifer(nname, override = true):
        result = sym.override

        if kind != nskProc:
          result = result.replace(re"(?m)^(.*?)$", "  $1")

proc getOverrideFinal*(nimState: NimState, kind: NimSymKind): string =
  let
    typ = $kind

  if nimState.gState.onSymbolOverrideFinal != nil:
    for i in nimState.gState.onSymbolOverrideFinal(typ):
      result &= "\n" & nimState.getOverride(i, kind)

proc getLit*(str: string): PNode =
  # Used to convert #define literals into const
  let
    str = str.replace(re"/[/*].*?(?:\*/)?$", "").strip()

  if str.contains(re"^[\-]?[\d]+$"):              # decimal
    result = newIntNode(nkIntLit, parseInt(str))

  elif str.contains(re"^[\-]?[\d]*[.]?[\d]+$"):   # float
    result = newFloatNode(nkFloatLit, parseFloat(str))

  # TODO - hex becomes int on render
  elif str.contains(re"^0x[\da-fA-F]+$"):         # hexadecimal
    result = newIntNode(nkIntLit, parseHexInt(str))

  elif str.contains(re"^'[[:ascii:]]'$"):         # char
    result = newNode(nkCharLit)
    result.intVal = str[1].int64

  elif str.contains(re"""^"[[:ascii:]]+"$"""):    # char *
    result = newStrNode(nkStrLit, str[1 .. ^2])

  else:
    result = newNode(nkNilLit)

# TSNode shortcuts

proc len*(node: TSNode): uint =
  if not node.tsNodeIsNull:
    result = node.tsNodeNamedChildCount().uint

proc `[]`*(node: TSNode, i: BiggestUInt): TSNode =
  if i < node.len():
    result = node.tsNodeNamedChild(i.uint32)

proc getName*(node: TSNode): string {.inline.} =
  if not node.tsNodeIsNull:
    return $node.tsNodeType()

proc getNodeVal*(nimState: NimState, node: TSNode): string =
  if not node.tsNodeIsNull:
    return nimState.gState.code[node.tsNodeStartByte() .. node.tsNodeEndByte()-1].strip()

proc getAtom*(node: TSNode): TSNode =
  if not node.tsNodeIsNull:
    # Get child node which is topmost atom
    if node.getName() in gAtoms:
      return node
    elif node.len() != 0:
      return node[0].getAtom()

proc getPtrCount*(node: TSNode): string =
  if not node.tsNodeIsNull:
    # Get number of ptr nodes in tree
    var
      cnode = node
    while "pointer_declarator" in cnode.getName():
      result &= "ptr "
      if cnode.len() != 0:
        cnode = cnode[0]
      else:
        break

proc getDeclarator*(node: TSNode): TSNode =
  if not node.tsNodeIsNull:
    # Return if child is a function or array declarator
    if node.getName() in ["function_declarator", "array_declarator"]:
      return node
    elif node.len() != 0:
      return node[0].getDeclarator()

proc inTree*(node: TSNode, ntype: string): bool =
  # Search for node type in tree - first children
  result = false
  var
    cnode = node
  while not cnode.tsNodeIsNull:
    if cnode.getName() == ntype:
      return true
    cnode = cnode[0]

proc inChildren*(node: TSNode, ntype: string): bool =
  # Search for node type in immediate children
  result = false
  for i in 0 ..< node.len():
    if (node[i]).getName() == ntype:
      result = true
      break

proc getLineCol*(gState: State, node: TSNode): tuple[line, col: int] =
  # Get line number and column info for node
  result.line = 1
  result.col = 1
  for i in 0 .. node.tsNodeStartByte().int-1:
    if gState.code[i] == '\n':
      result.col = 0
      result.line += 1
    result.col += 1

proc getTSNodeNamedChildCountSansComments*(node: TSNode): int =
  for i in 0 ..< node.len():
    if node.getName() != "comment":
      result += 1

proc getPxName*(node: TSNode, offset: int): string =
  # Get the xth (grand)parent of the node
  var
    np = node
    count = 0

  while not np.tsNodeIsNull() and count < offset:
    np = np.tsNodeParent()
    count += 1

  if count == offset and not np.tsNodeIsNull():
    return np.getName()

proc printLisp*(gState: State, root: TSNode): string =
  var
    node = root
    nextnode: TSNode
    depth = 0

  while true:
    if not node.tsNodeIsNull() and depth > -1:
      if gState.pretty:
        result &= spaces(depth)
      let
        (line, col) = gState.getLineCol(node)
      result &= &"({$node.tsNodeType()} {line} {col} {node.tsNodeEndByte() - node.tsNodeStartByte()}"
    else:
      break

    if node.tsNodeNamedChildCount() != 0:
      if gState.pretty:
        result &= "\n"
      nextnode = node.tsNodeNamedChild(0)
      depth += 1
    else:
      if gState.pretty:
        result &= ")\n"
      else:
        result &= ")"
      nextnode = node.tsNodeNextNamedSibling()

    if nextnode.tsNodeIsNull():
      while true:
        node = node.tsNodeParent()
        depth -= 1
        if depth == -1:
          break
        if gState.pretty:
          result &= spaces(depth) & ")\n"
        else:
          result &= ")"
        if node == root:
          break
        if not node.tsNodeNextNamedSibling().tsNodeIsNull():
          node = node.tsNodeNextNamedSibling()
          break
    else:
      node = nextnode

    if node == root:
      break

proc getCommented*(str: string): string =
  "\n# " & str.strip().replace("\n", "\n# ")

proc printTree*(nimState: NimState, pnode: PNode, offset = "") =
  if nimState.gState.debug and pnode.kind != nkNone:
    stdout.write "\n# " & offset & $pnode.kind & "("
    case pnode.kind
    of nkCharLit:
      stdout.write "'" & pnode.intVal.char & "')"
    of nkIntLit..nkUInt64Lit:
      stdout.write $pnode.intVal & ")"
    of nkFloatLit..nkFloat128Lit:
      stdout.write $pnode.floatVal & ")"
    of nkStrLit..nkTripleStrLit:
      stdout.write "\"" & pnode.strVal & "\")"
    of nkSym:
      stdout.write $pnode.sym & ")"
    of nkIdent:
      stdout.write "\"" & $pnode.ident.s & "\")"
    else:
      if pnode.sons.len != 0:
        for i in 0 ..< pnode.sons.len:
          nimState.printTree(pnode.sons[i], offset & " ")
          if i != pnode.sons.len - 1:
            stdout.write ","
        stdout.write "\n# " & offset & ")"
      else:
        stdout.write ")"
    if offset.len == 0:
      echo ""

proc printDebug*(nimState: NimState, node: TSNode) =
  if nimState.gState.debug:
    echo nimState.getNodeVal(node).getCommented()
    echo nimState.gState.printLisp(node).getCommented()

proc printDebug*(nimState: NimState, pnode: PNode) =
  if nimState.gState.debug:
    echo ($pnode).getCommented()
    nimState.printTree(pnode)

# Compiler shortcuts

proc getLineInfo*(nimState: NimState, node: TSNode): TLineInfo =
  # Get Nim equivalent line:col info from node
  let
    (line, col) = nimState.gState.getLineCol(node)

  result = newLineInfo(nimState.config, nimState.sourceFile.AbsoluteFile, line, col)

proc getIdent*(nimState: NimState, name: string, info: TLineInfo, exported = true): PNode =
  # Get ident PNode for name + info
  let
    exp = getIdent(nimState.identCache, "*")
    ident = getIdent(nimState.identCache, name)

  if exported:
    result = newNode(nkPostfix)
    result.add newIdentNode(exp, info)
    result.add newIdentNode(ident, info)
  else:
    result = newIdentNode(ident, info)

proc getNameInfo*(nimState: NimState, node: TSNode, kind: NimSymKind, parent = ""):
  tuple[name: string, info: TLineInfo] =
  # Shortcut to get identifier name and info (node value and line:col)
  let
    name = nimState.getNodeVal(node)
  result.name = nimState.getIdentifier(name, kind, parent)
  result.info = nimState.getLineInfo(node)

proc getCurrentHeader*(fullpath: string): string =
  ("header" & fullpath.splitFile().name.multiReplace([(".", ""), ("-", "")]))

proc removeStatic(content: string): string =
  ## Replace static function bodies with a semicolon and commented
  ## out body
  return content.replace(
    re"(?msU)static inline ([^)]+\))([^}]+\})",
    proc (m: RegexMatch, s: string): string =
      let funcDecl = s[m.group(0)[0]]
      let body = s[m.group(1)[0]].strip()
      result = ""

      result.add("$#;" % [funcDecl])
      result.add(body.replace(re"(?m)^(.*\n?)", "//$1"))
  )

proc getPreprocessor*(gState: State, fullpath: string, mode = "cpp"): string =
  var
    mmode = if mode == "cpp": "c++" else: mode
    cmts = if gState.nocomments: "" else: "-CC"
    cmd = &"""{getCompiler()} -E {cmts} -dD -x{mmode} -w """

    rdata: seq[string] = @[]
    start = false
    sfile = fullpath.sanitizePath(noQuote = true)

  for inc in gState.includeDirs:
    cmd &= &"-I{inc.sanitizePath} "

  for def in gState.defines:
    cmd &= &"-D{def} "

  cmd &= &"{fullpath.sanitizePath}"

  # Include content only from file
  for line in execAction(cmd).output.splitLines():
    if line.strip() != "":
      if line.len > 1 and line[0 .. 1] == "# ":
        start = false
        let
          saniLine = line.sanitizePath(noQuote = true)
        if sfile in saniLine:
          start = true
        elif not ("\\" in line) and not ("/" in line) and extractFilename(sfile) in line:
          start = true
        elif gState.recurse:
          let
            pDir = sfile.expandFilename().parentDir().sanitizePath(noQuote = true)
          if pDir.Bl or pDir in saniLine:
            start = true
          else:
            for inc in gState.includeDirs:
              if inc.absolutePath().sanitizePath(noQuote = true) in saniLine:
                start = true
                break
      else:
        if start:
          if "#undef" in line:
            continue
          rdata.add line
  return rdata.join("\n").
    replace("__restrict", "").
    replace(re"__attribute__[ ]*\(\(.*?\)\)([ ,;])", "$1").
    removeStatic()

proc getNimExpression*(nimState: NimState, expr: string): string =
  var
    clean = expr.multiReplace([("\n", " "), ("\r", "")])
    ident = ""
    gen = ""
    hex = false

  for i in 0 .. clean.len:
    if i != clean.len:
      if clean[i] in IdentChars:
        if clean[i] in Digits and ident.Bl:
          # Identifiers cannot start with digits
          gen = $clean[i]
        elif clean[i] in HexDigits and hex == true:
          # Part of a hex number
          gen = $clean[i]
        elif i > 0 and i < clean.len-1 and clean[i] in ['x', 'X'] and
              clean[i-1] == '0' and clean[i+1] in HexDigits:
          # Found a hex number
          gen = $clean[i]
          hex = true
        else:
          # Part of an identifier
          ident &= clean[i]
          hex = false
      else:
        gen = (block:
          if (i == 0 or clean[i-1] != '\'') or
            (i == clean.len - 1 or clean[i+1] != '\''):
              # If unquoted, convert logical ops to Nim
              case clean[i]
              of '^': " xor "
              of '&': " and "
              of '|': " or "
              of '~': " not "
              else: $clean[i]
          else:
            $clean[i]
        )
        hex = false

    if i == clean.len or gen.nBl:
      # Process identifier
      if ident.nBl:
        ident = nimState.getIdentifier(ident, nskConst)
        result &= ident
        ident = ""
      result &= gen
      gen = ""

  # Convert shift ops to Nim
  result = result.multiReplace([
    ("<<", " shl "), (">>", " shr ")
  ])

proc getSplitComma*(joined: seq[string]): seq[string] =
  for i in joined:
    result = result.concat(i.split(","))

proc getComments*(nimState: NimState, strip = false): string =
  if not nimState.gState.nocomments and nimState.commentStr.nBl:
    result = "\n" & nimState.commentStr
    if strip:
      result = result.replace("\n  ", "\n")
    nimState.commentStr = ""

proc dll*(path: string): string =
  let
    (dir, name, _) = path.splitFile()

  result = dir / (DynlibFormat % name)

proc loadPlugin*(gState: State, sourcePath: string) =
  doAssert fileExists(sourcePath), "Plugin file does not exist: " & sourcePath

  let
    pdll = sourcePath.dll
  if not fileExists(pdll) or
    sourcePath.getLastModificationTime() > pdll.getLastModificationTime():
    discard execAction(&"{gState.nim.sanitizePath} c --app:lib {sourcePath.sanitizePath}")
  doAssert fileExists(pdll), "No plugin binary generated for " & sourcePath

  let lib = loadLib(pdll)
  doAssert lib != nil, "Plugin $1 compiled to $2 failed to load" % [sourcePath, pdll]

  gState.onSymbol = cast[OnSymbol](lib.symAddr("onSymbol"))

  gState.onSymbolOverride = cast[OnSymbol](lib.symAddr("onSymbolOverride"))

  gState.onSymbolOverrideFinal = cast[OnSymbolOverrideFinal](lib.symAddr("onSymbolOverrideFinal"))

proc expandSymlinkAbs*(path: string): string =
  try:
    result = path.expandSymlink().absolutePath(path.parentDir()).myNormalizedPath()
  except:
    result = path
