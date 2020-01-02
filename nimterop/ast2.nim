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

proc newPtrTree(count: int): tuple[parent, child: PNode] =
  # Create nkPtrTy tree depending on count
  #
  # nkPtrTy(
  #  nkPtrTy(
  #  ..
  #  )
  # )
  if count > 0:
    result.parent = newNode(nkPtrTy)
    result.child = result.parent
    for i in 1 ..< count:
      let
        child = newNode(nkPtrTy)
      result.child.add child
      result.child = child

proc addType0(nimState: NimState, node: TSNode) =
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

proc addType1(nimState: NimState, node: TSNode) =
  let
    # node[1] = identifer = name
    typeDef = nimState.newTypeIdent(node[1])

    # node[0] = identifier = type name
    (name, info) = nimState.getNameInfo(node[0].getAtom(), nskType)
    # TODO - check blank and override
    # TODO - use getPtrType() - ptr cchar to cstring
    ident = nimState.getIdent(name, info, exported = false)

    # node[1] could have pointers
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

  if count > 0:
    let
      (parent, child) = newPtrTree(count)
    child.add ident
    typeDef.add parent
  else:
    typeDef.add ident

  # nkTypeSection.add
  nimState.typeSection.add typeDef

  nimState.printDebug(typeDef)

proc addType(nimState: NimState, node: TSNode) =
  # CASE1:
  #
 #
  # CASE 2
  #
  # typedef struct X *Y;
  #
  # (type_definition
  #  (struct_specifier
  #   (type_identifier)
  #  )
  #  (pointer_declarator
  #   (type_identifier)
  #  )
  # )
  #
  nimState.printDebug(node)

  if node.getName() == "struct_specifier":
    if node.len == 1:
      # struct X;
      #
      # (struct_specifier
      #  (type_identifier)
      # )
      nimState.addType0(node)
    elif node.len == 2:
      if node[1].getName() == "field_declaration_list" and node[1].len == 0:
        # struct X {};
        #
        # (struct_specifier
        #  (type_identifier)
        #  (field_declaration_list = "{}")
        # )
        nimState.addType0(node)
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
          nimState.addType0(node)
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
          nimState.addType0(node)
      else:
        let
          sspec = node[0].firstChildInTree("struct_specifier")
          adecl = node[1].anyChildInTree("array_declarator")
          fdecl = node[1].anyChildInTree("function_declarator")
        if fdlist.isNil():
          if adecl.isNil and fdecl.isNil:
            if not sspec.isNil:
              # typedef struct X [*]Y;
              #
              # (type_definition
              #  (struct_specifier
              #   (type_identifier)
              #  )
              #  (pointer_declarator - optional, nested
              #   (type_identifier)
              #  )
              # )
              nimState.addType1(node)
            else:
              # typedef struct int Y;
              #
              # (type_definition
              #  (type_identifier|primitive_type)
              #  (pointer_declarator - optional, nested
              #   (type_identifier)
              #  )
              # )
              nimState.addType1(node)
          elif not adecl.isNil:
            # typedef X Y[a][..];
            #
            # (type_definition
            #  (struct_specifier
            #   (type_identifier)
            #  )
            #  (pointer_declarator
            #   (array_declarator
            #    (type_identifier)
            #    (number_literal)
            #   )
            #  )
            # )
            discard

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
