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
  # Create nkBracketExpr tree depending on input
  #
  # nkBracketExpr(
  #  nkIdent("array"),
  #  size,
  #  typ
  # )
  result = newNode(nkBracketExpr)

  let
    (_, info) = nimState.getNameInfo(node, nskType)
    ident = nimState.getIdent("array", info, exported = false)

  result.add ident
  result.add size
  result.add typ

proc getTypeArray(nimState: NimState, node: TSNode): PNode
proc getTypeProc(nimState: NimState, node: TSNode, name: string): PNode

proc newProcParam(nimState: NimState, name: string, node: TSNode, offset: uint64): PNode =
  # Create nkIdentDefs tree for specified parameter
  result = newNode(nkIdentDefs)

  let
    # node[0] - param type
    (tname, tinfo) = nimState.getNameInfo(node[0], nskType)
    tident = nimState.getIdent(tname, tinfo, exported = false)

  if node.len == 1:
    let
      pname = "a" & $(offset+1)
      pident = nimState.getIdent(pname, tinfo, exported = false)
    result.add pident
    result.add tident
    result.add newNode(nkEmpty)
  else:
    let
      fdecl = node[1].anyChildInTree("function_declarator")
      adecl = node[1].anyChildInTree("array_declarator")
      abst = node[1].getName() == "abstract_pointer_declarator"
    if fdecl.isNil and adecl.isNil:
      if abst:
        let
          pname = "a" & $(offset+1)
          pident = nimState.getIdent(pname, tinfo, exported = false)
          acount = node[1].getXCount("abstract_pointer_declarator")
        result.add pident
        result.add newPtrTree(acount, tident)
        result.add newNode(nkEmpty)
      else:
        let
          (pname, pinfo) = nimState.getNameInfo(node[1].getAtom(), nskField, parent = name)
          pident = nimState.getIdent(pname, pinfo, exported = false)

          count = node[1].getPtrCount()
        result.add pident
        if count > 0:
          result.add newPtrTree(count, tident)
        else:
          result.add tident
        result.add newNode(nkEmpty)
    elif not fdecl.isNil:
      let
        (pname, pinfo) = nimState.getNameInfo(node[1].getAtom(), nskField, parent = name)
        pident = nimState.getIdent(pname, pinfo, exported = false)
      result.add pident
      result.add nimState.getTypeProc(node, name)
      result.add newNode(nkEmpty)
    elif not adecl.isNil:
      let
        (pname, pinfo) = nimState.getNameInfo(node[1].getAtom(), nskField, parent = name)
        pident = nimState.getIdent(pname, pinfo, exported = false)
      result.add pident
      result.add nimState.getTypeArray(node)
      result.add newNode(nkEmpty)
    else:
      result = nil

proc newProcTree(nimState: NimState, name: string, node: TSNode, rtyp: PNode): PNode =
  result = newNode(nkProcTy)

  let
    fparam = newNode(nkFormalParams)
  result.add fparam
  result.add newNode(nkEmpty)

  # Add return type
  fparam.add rtyp

  if not node.isNil:
    for i in 0 ..< node.len:
      let
        a = nimState.newProcParam(name, node[i], i)
      if not a.isNil:
        fparam.add a

proc addTypeObject(nimState: NimState, node: TSNode) =
  # Add a type of object
  let
    # TODO - check blank and override
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
    # TODO - check blank and override
    typeDef = nimState.newTypeIdent(node[1])

    # node[0] = identifier = type name
    (name, info) = nimState.getNameInfo(node[0].getAtom(), nskType)
    ident = nimState.getIdent(name, info, exported = false)

    # node[1] could have nested pointers
    count = node[1].getPtrCount()

  # Skip typedef X X;
  if $typeDef[0][1] != name:
    if count > 0:
      # If pointers
      typeDef.add newPtrTree(count, ident)
    else:
      typeDef.add ident

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

    # nkTypeSection.add
    nimState.typeSection.add typeDef

    nimState.printDebug(typeDef)

proc getTypeArray(nimState: NimState, node: TSNode): PNode =
  # Create array type tree
  let
    # node[0] = identifier = type name
    (name, info) = nimState.getNameInfo(node[0].getAtom(), nskType)
    ident = nimState.getIdent(name, info, exported = false)

    # Top-most array declarator
    adecl = node[1].firstChildInTree("array_declarator")

    # node[1] could have nested arrays
    acount = adecl.getArrayCount()
    innermost = adecl.mostNestedChildInTree()

    # node[1] could have nested pointers - type
    tcount = node[1].getPtrCount()

    # Name could be nested pointer to array
    #
    # (..
    #  (array_declarator
    #   (parenthesized_declarator
    #    (pointer_declarator ..
    #     (pointer_declarator          <- search upwards from atom
    #      (type_identifier)           <- atom
    #     )
    #    )
    #   )
    #  )
    # )
    ncount = innermost[0].getAtom().tsNodeParent().getPtrCount(reverse = true)

  result = ident
  var
    cnode = adecl

  if tcount > 0:
    # If pointers
    result = newPtrTree(tcount, result)

  for i in 0 ..< acount:
    let
      size = nimState.getNodeVal(cnode[1]).getLit()
    if size.kind != nkNilLit:
      result = nimState.newArrayTree(cnode, result, size)
      cnode = cnode[0]

  if ncount > 0:
    result = newPtrTree(ncount, result)

proc addTypeArray(nimState: NimState, node: TSNode) =
  # Add a type of array type
  let
    # node[1] = identifer = name
    # TODO - check blank and override
    typeDef = nimState.newTypeIdent(node[1])

    typ = nimState.getTypeArray(node)

  typeDef.add typ

  # type X* = [ptr] array[x, [ptr] Y]
  #
  # nkTypeDef(
  #  nkPostfix(
  #   nkIdent("*"),
  #   nkIdent("X")
  #  ),
  #  nkEmpty(),
  #  nkPtrTy(              # optional, nested
  #   nkBracketExpr(
  #    nkIdent("array")
  #    nkXLit(x),
  #    nkPtrTy(            # optional, nested
  #     nkIdent("Y")
  #    )
  #   )
  #  )
  # )

  # nkTypeSection.add
  nimState.typeSection.add typeDef

  nimState.printDebug(typeDef)

proc getTypeProc(nimState: NimState, node: TSNode, name: string): PNode =
  # Create proc type tree
  let
    # node[0] = identifier = return type name
    (rname, rinfo) = nimState.getNameInfo(node[0].getAtom(), nskType)

    # Parameter list
    plist = node[1].anyChildInTree("parameter_list")

    # node[1] could have nested pointers
    tcount = node[1].getPtrCount()

    # Name could be nested pointer to function
    #
    # (..
    #  (function_declarator
    #   (parenthesized_declarator
    #    (pointer_declarator ..
    #     (pointer_declarator          <- search upwards from atom
    #      (type_identifier)           <- atom
    #     )
    #    )
    #   )
    #  )
    # )
    ncount = node[1].getAtom().tsNodeParent().getPtrCount(reverse = true)

  # Return type
  var
    retType = nimState.getIdent(rname, rinfo, exported = false)
  if tcount > 0:
    retType = newPtrTree(tcount, retType)

  # Proc with return type and params
  result = nimState.newProcTree(name, plist, retType)
  if ncount > 1:
    result = newPtrTree(ncount-1, result)

proc addTypeProc(nimState: NimState, node: TSNode) =
  # Add a type of proc type
  let
    # node[1] = identifier = name
    # TODO - check blank and override
    typeDef = nimState.newTypeIdent(node[1])
    name = $typeDef[0][1]

    procTy = nimState.getTypeProc(node, name)

  typeDef.add procTy

  # type X* = proc(a1: Y, a2: Z): P
  #
  # nkTypeDef(
  #  nkPostfix(
  #   nkIdent("*"),
  #   nkIdent("X")
  #  ),
  #  nkEmpty(),
  #  nkPtrTy(              # optional, nested
  #   nkProcTy(
  #    nkFormalParams(
  #     nkPtrTy(           # optional, nested
  #      nkIdent(retType)
  #     ),
  #     nkIdentDefs(
  #      nkIdent(param),
  #      nkPtrTy(
  #       nkIdent(ptype)
  #      ),
  #      nkEmpty()
  #     ),
  #     ...
  #    ),
  #    nkEmpty()
  #   )
  #  )
  # )

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
          fdecl = node[1].anyChildInTree("function_declarator")
          adecl = node[1].anyChildInTree("array_declarator")
        if fdlist.isNil():
          if adecl.isNil and fdecl.isNil:
            # typedef X Y;
            # typedef X *Y;
            # typedef struct X Y;
            # typedef struct X *Y;
            #
            # (type_definition
            #  (type_identifier|primitive_type|)
            #  (struct_specifier
            #   (type_identifier)
            #  )
            #
            #  (pointer_declarator - optional, nested
            #   (type_identifier)
            #  )
            # )
            nimState.addTypeTyped(node)
          elif not fdecl.isNil:
            # typedef X (*Y)(a1, a2, a3);
            # typedef X *(*Y)(a1, a2, a3);
            # typedef struct X (*Y)(a1, a2, a3);
            # typedef struct X *(*Y)(a1, a2, a3);
            #
            # (type_definition
            #  (type_identifier|primitive_type|)
            #  (struct_specifier
            #   (type_identifier)
            #  )
            #
            #  (pointer_declarator - optional, nested
            #   (function_declarator
            #    (parenthesized_declarator
            #     (pointer_declarator
            #      (type_identifer)
            #     )
            #    )
            #    (parameter_list
            #     (parameter_declaration
            #      (struct_specifier|type_identifier|primitive_type|array_declarator|function_declarator)
            #      (identifier - optional)
            #     )
            #    )
            #   )
            #  )
            # )
            nimState.addTypeProc(node)
          elif not adecl.isNil:
            # typedef struct X Y[a][..];
            # typedef struct X *Y[a][..];
            # typedef struct X *(*Y)[a][..];
            #
            # (type_definition
            #  (type_identifier|primitive_type|)
            #  (struct_specifier
            #   (type_identifier)
            #  )
            #
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
