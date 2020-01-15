import sequtils, sets, tables

import regex

import "."/plugin

when not declared(CIMPORT):
  import compiler/[ast, idents, options]
  import "."/treesitter/api

const
  gAtoms {.used.} = @[
    "field_identifier",
    "identifier",
    "number_literal",
    "char_literal",
    "preproc_arg",
    "primitive_type",
    "sized_type_specifier",
    "type_identifier"
  ].toSet()

  gExpressions {.used.} = @[
    "parenthesized_expression",
    "bitwise_expression",
    "shift_expression",
    "math_expression",
    "escape_sequence"
  ].toSet()

  gEnumVals {.used.} = @[
    "identifier",
    "number_literal",
    "char_literal"
  ].concat(toSeq(gExpressions.items))

type
  State = ref object
    compile*, defines*, headers*, includeDirs*, searchDirs*, prefix*, suffix*, symOverride*: seq[string]

    nocache*, nocomments*, debug*, past*, preprocess*, pnim*, pretty*, recurse*: bool

    code*, dynlib*, mode*, nim*, overrides*, pluginSource*, pluginSourcePath*: string

    onSymbol*, onSymbolOverride*: OnSymbol
    onSymbolOverrideFinal*: OnSymbolOverrideFinal

    outputHandle*: File

  NimState {.used.} = ref object
    identifiers*: TableRef[string, string]

    commentStr*, debugStr*, skipStr*: string

    # Nim compiler objects
    when not declared(CIMPORT):
      constSection*, enumSection*, procSection*, typeSection*: PNode
      identCache*: IdentCache
      config*: ConfigRef

    gState*: State

    currentHeader*, impShort*, sourceFile*: string

    data*: seq[tuple[name, val: string]]

    nodeBranch*: seq[string]

var
  gStateCT {.compiletime, used.} = new(State)

template nBl(s: typed): untyped {.used.} =
  (s.len != 0)

template Bl(s: typed): untyped {.used.} =
  (s.len == 0)

type CompileMode = enum
  c,
  cpp,

# TODO: can cligen accept enum instead of string?
const modeDefault {.used.} = $cpp # TODO: USE this everywhere relevant

when not declared(CIMPORT):
  export gAtoms, gExpressions, gEnumVals, State, NimState,
    nBl, Bl, CompileMode, modeDefault

  # Redirect output to file when required
  template gecho*(args: string) {.dirty.} =
    if gState.outputHandle.isNil:
      echo args
    else:
      gState.outputHandle.writeLine(args)

  template necho*(args: string) {.dirty.} =
    let gState = nimState.gState
    gecho args

  template decho*(str: untyped): untyped =
    if nimState.gState.debug:
      let gState = nimState.gState
      necho str.getCommented()
