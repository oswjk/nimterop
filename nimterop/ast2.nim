import macros, os, strutils, tables, times

import compiler/[ast, astalgo, idents, options, renderer]

import "."/treesitter/api

import "."/[compat, globals, getters]

proc addConst(nimState: NimState, node: TSNode) =
  # #define X Y
  #
  # (preproc_def
  #  (identifier)
  #  (preproc_arg)
  # )
  nimState.printDebug(node)

  if node[0].getName() == "identifier" and
    node[1].getName() == "preproc_arg":
    let
      constDef = newNode(nkConstDef)

      # node[0] = identifier = const name
      (name, info) = nimState.getNameInfo(node.getAtom(), nskConst)
      # TODO - check blank and override
      ident = nimState.getIdent(name, info)

      # node[1] = preproc_arg = value
      val = nimState.getNodeVal(node[1]).getLit()

    # If supported literal
    if val.kind != nkNilLit:
      # const X* = Y
      #
      # nkConstDef(
      #  nkPostfix(
      #   nkIdent("*"),
      #   nkIdent("X")
      #  ),
      #  nkEmpty(),
      #  nkXLit(Y)
      # )
      constDef.add ident
      constDef.add newNode(nkEmpty)
      constDef.add val

      # nkConstSection.add
      nimState.constSection.add constDef

      nimState.printDebug(constDef)

proc newTypeIdent(nimState: NimState, node: TSNode): PNode =
  # Create nkTypeDef PNode with first ident
  let
    (name, info) = nimState.getNameInfo(node.getAtom(), nskType)
    # TODO - check blank and override
    ident = nimState.getIdent(name, info)

  result = newNode(nkTypeDef)
  result.add ident
  result.add newNode(nkEmpty)

proc newPtrTree(count: int, typ: PNode): PNode =
  # Create nkPtrTy tree depending on count
  #
  # Reduce by 1 if Nim type available for ptr X - e.g. ptr cchar = cstring
  #
  # nkPtrTy(
  #  nkPtrTy(
  #    typ
  #  )
  # )
  var
    count = count
  if typ.kind == nkIdent:
    let
      tname = typ.ident.s
      ptname = getPtrType(tname)
    if tname != ptname:
      typ.ident.s = ptname
      count -= 1
  if count > 0:
    result = newNode(nkPtrTy)
    var
      parent = result
      child: PNode
    for i in 1 ..< count:
      child = newNode(nkPtrTy)
      parent.add child
      parent = child
    parent.add typ
  else:
    result = typ

proc newArrayTree(nimState: NimState, node: TSNode, typ, size: PNode): PNode =
  result = newNode(nkBracketExpr)

  let
    (_, info) = nimState.getNameInfo(node, nskType)
    ident = nimState.getIdent("array", info, exported = false)

  result.add ident
  result.add size
  result.add typ

proc addTypeObject(nimState: NimState, node: TSNode) =
  # Add a type of object
  let
    typeDef = nimState.newTypeIdent(node)

  # type X* = object
  #
  # nkTypeDef(
  #  nkPostfix(
  #   nkIdent("*"),
  #   nkIdent("X")
  #  ),
  #  nkEmpty(),
  #  nkObjectTy(
  #   nkEmpty(),
  #   nkEmpty(),
  #   nkEmpty()
  #  )
  # )
  typeDef.add(block:
    let
      obj = newNode(nkObjectTy)
    obj.add newNode(nkEmpty)
    obj.add newNode(nkEmpty)
    obj.add newNode(nkEmpty)

    obj
  )

  # nkTypeSection.add
  nimState.typeSection.add typeDef

  nimState.printDebug(typeDef)

proc addTypeTyped(nimState: NimState, node: TSNode) =
  # Add a type of a specific type
  let
    # node[1] = identifer = name
    typeDef = nimState.newTypeIdent(node[1])

    # node[0] = identifier = type name
    (name, info) = nimState.getNameInfo(node[0].getAtom(), nskType)
    # TODO - check blank and override
    ident = nimState.getIdent(name, info, exported = false)

    # node[1] could have nested pointers
    count = node[1].getPtrCount()

  # type X* = [ptr ..] Y
  #
  # nkTypeDef(
  #  nkPostfix(
  #   nkIdent("*"),
  #   nkIdent("X")
  #  ),
  #  nkEmpty(),
  #  nkPtrTy(            # optional, nested
  #   nkIdent("Y")
  #  )
  # )

  # Skip typedef X X;
  if $typeDef[0][1] != name:
    if count > 0:
      # If pointers
      typeDef.add newPtrTree(count, ident)
    else:
      typeDef.add ident

    # nkTypeSection.add
    nimState.typeSection.add typeDef

    nimState.printDebug(typeDef)

proc addTypeArray(nimState: NimState, node: TSNode) =
  # Add a type of a array type
  let
    # node[1] = identifer = name
    typeDef = nimState.newTypeIdent(node[1])

    # node[0] = identifier = type name
    (name, info) = nimState.getNameInfo(node[0].getAtom(), nskType)
    # TODO - check blank and override
    ident = nimState.getIdent(name, info, exported = false)

    # Top-most array declarator
    adecl = node[1].firstChildInTree("array_declarator")

    # node[1] could have nested arrays
    acount = adecl.getArrayCount()
    innermost = adecl.mostNestedChildInTree()

    # node[1] could have nested pointers - type
    tcount = node[1].getPtrCount()

    # Name could have nested pointers
    ncount = innermost[0].getPtrCount()

  var
    cnode = adecl
    typ = ident

  if tcount > 0:
    # If pointers
    typ = newPtrTree(tcount, typ)

  for i in 0 ..< acount:
    let
      size = nimState.getNodeVal(cnode[1]).getLit()
    if size.kind != nkNilLit:
      typ = nimState.newArrayTree(cnode, typ, size)
      cnode = cnode[0]

  if ncount > 0:
    typ = newPtrTree(ncount, typ)

  typeDef.add typ

  # nkTypeSection.add
  nimState.typeSection.add typeDef

  nimState.printDebug(typeDef)

proc addType(nimState: NimState, node: TSNode) =
  nimState.printDebug(node)

  if node.getName() == "struct_specifier":
    if node.len == 1:
      # struct X;
      #
      # (struct_specifier
      #  (type_identifier)
      # )
      nimState.addTypeObject(node)
    elif node.len == 2:
      if node[1].getName() == "field_declaration_list" and node[1].len == 0:
        # struct X {};
        #
        # (struct_specifier
        #  (type_identifier)
        #  (field_declaration_list = "{}")
        # )
        nimState.addTypeObject(node)
  elif node.getName() == "type_definition":
    if node.len == 2:
      let
        fdlist = node[0].anyChildInTree("field_declaration_list")
      if nimState.getNodeVal(node[1]) == "":
        if fdlist.isNil():
          # typedef struct X;
          #
          # (type_definition
          #  (struct_specifier
          #   (type_identifier)
          #  )
          #  (type_definition = "")
          # )
          nimState.addTypeObject(node)
        elif fdlist.len == 0:
          # typedef struct X {};
          #
          # (type_definition
          #  (struct_specifier
          #   (type_identifier)
          #   (field_declaration_list = "{}")
          #  )
          #  (type_definition = "")
          # )
          nimState.addTypeObject(node)
      else:
        let
          sspec = node[0].firstChildInTree("struct_specifier")
          fdecl = node[1].anyChildInTree("function_declarator")
          adecl = node[1].anyChildInTree("array_declarator")
        if fdlist.isNil():
          if adecl.isNil and fdecl.isNil:
            if not sspec.isNil:
              # typedef struct X Y;
              # typedef struct X *Y;
              #
              # (type_definition
              #  (struct_specifier
              #   (type_identifier)
              #  )
              #  (pointer_declarator - optional, nested
              #   (type_identifier)
              #  )
              # )
              nimState.addTypeTyped(node)
            else:
              # typedef X Y;
              # typedef X *Y;
              #
              # (type_definition
              #  (type_identifier|primitive_type)
              #  (pointer_declarator - optional, nested
              #   (type_identifier)
              #  )
              # )
              nimState.addTypeTyped(node)
          elif not fdecl.isNil:
            discard
          elif not adecl.isNil:
            if not sspec.isNil:
              # typedef struct X Y[a][..];
              # typedef struct X *Y[a][..];
              # typedef struct X *(*Y)[a][..];
              #
              # (type_definition
              #  (struct_specifier
              #   (type_identifier)
              #  )
              #  (pointer_declarator - optional, nested
              #   (array_declarator - nested
              #    (pointer_declarator - optional, nested
              #     (type_identifier)
              #    )
              #    (number_literal)
              #   )
              #  )
              # )
              nimState.addTypeArray(node)
            else:
              # typedef X Y[a][..];
              # typedef X *Y[a][..];
              # typedef X *(*Y)[a][..];
              #
              # (type_definition
              #  (type_identifier|primitive_type)
              #  (pointer_declarator - optional, nested
              #   (array_declarator - nested
              #    (pointer_declarator - optional, nested
              #     (type_identifier)
              #    )
              #    (number_literal)
              #   )
              #  )
              # )
              nimState.addTypeArray(node)

proc addEnum(nimState: NimState, node: TSNode) =
  nimState.printDebug(node)

proc addProc(nimState: NimState, node: TSNode) =
  nimState.printDebug(node)

proc processNode(nimState: NimState, node: TSNode): bool =
  result = true

  case node.getName()
  of "preproc_def":
    nimState.addConst(node)
  of "type_definition":
    if not node.firstChildInTree("enum_specifier").isNil():
      nimState.addEnum(node)
    else:
      nimState.addType(node)
  of "struct_specifier":
    nimState.addType(node)
  of "enum_specifier":
    nimState.addEnum(node)
  of "declaration":
    nimState.addProc(node)
  else:
    # Unknown
    result = false

proc searchTree(nimState: NimState, root: TSNode) =
  # Search AST generated by tree-sitter for recognized elements
  var
    node = root
    nextnode: TSNode
    depth = 0
    processed = false

  while true:
    if not node.isNil() and depth > -1:
      processed = nimState.processNode(node)
    else:
      break

    if not processed and node.len() != 0:
      nextnode = node[0]
      depth += 1
    else:
      nextnode = node.tsNodeNextNamedSibling()

    if nextnode.isNil():
      while true:
        node = node.tsNodeParent()
        depth -= 1
        if depth == -1:
          break
        if node == root:
          break
        if not node.tsNodeNextNamedSibling().isNil():
          node = node.tsNodeNextNamedSibling()
          break
    else:
      node = nextnode

    if node == root:
      break

proc printNimHeader*() =
  echo """# Generated at $1
# Command line:
#   $2 $3

{.hint[ConvFromXtoItselfNotNeeded]: off.}

import nimterop/types
""" % [$now(), getAppFilename(), commandLineParams().join(" ")]

proc printNim*(gState: State, fullpath: string, root: TSNode) =
  var
    nimState = new(NimState)
    fp = fullpath.replace("\\", "/")

  nimState.identifiers = newTable[string, string]()

  nimState.gState = gState
  nimState.currentHeader = getCurrentHeader(fullpath)
  nimState.sourceFile = fullpath

  # Nim compiler objects
  nimState.identCache = newIdentCache()
  nimState.config = newConfigRef()

  nimState.constSection = newNode(nkConstSection)
  nimState.enumSection = newNode(nkStmtList)
  nimState.procSection = newNode(nkStmtList)
  nimState.typeSection = newNode(nkTypeSection)

  nimState.searchTree(root)

  var
    tree = newNode(nkStmtList)
  tree.add nimState.enumSection
  tree.add nimState.constSection
  tree.add nimState.typeSection
  tree.add nimState.procSection

  echo tree.renderTree()
