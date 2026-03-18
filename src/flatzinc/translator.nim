## FlatZinc translator - maps FznModel to ConstraintSystem[int].

import std/[tables, sequtils, strutils, strformat, packedsets, sets, math, algorithm, hashes]

import parser
import dfaExtract
import ../constraintSystem
import ../constrainedArray
import ../constraints/[stateful, constraintNode, relationalConstraint, countEq, matrixElement, elementState, tableConstraint, noOverlapFixedBox, conditionalCumulative, conditionalNoOverlap, conditionalDayCapacity, disjunctiveClause, valueSupport, multiResourceNoOverlap]
import ../expressions/[expressions, algebraic, sumExpression, minExpression, maxExpression, weightedSameValue]

const
    ObjPosNone* = -2          ## No objective (satisfy problem)
    ObjPosDefinedExpr* = -1   ## Objective is a defined-variable expression
    ObjPosWeightedSV* = -3    ## Objective is a WeightedSameValueExpression

type
    CountEqPattern* = object
        ## A detected count_eq pattern from int_lin_eq → bool2int → int_eq_reif chains
        linEqIdx*: int           # index of the int_lin_eq constraint
        countValue*: int         # the constant value being counted
        targetVarName*: string   # name of the target variable (the count)
        arrayVarNames*: seq[string]  # names of the array variables being counted over

    ConditionalCountEqPattern* = object
        ## A detected conditional count_eq pattern:
        ## int_lin_eq → bool2int → array_bool_and → (int_eq_reif × 2) chains
        linEqIdx*: int           # index of the int_lin_eq constraint
        targetValue*: int        # value counted on primary positions
        filterValue*: int        # required value at filter positions
        targetVarName*: string   # name of the target variable (the count)
        primaryVarNames*: seq[string]  # names of primary condition variables (paired with filter)
        filterVarNames*: seq[string]   # names of filter condition variables (paired with primary)
        primaryOnlyVarNames*: seq[string]  # names of direct-path variables (no filter check)
        constantOffset*: int     # constant added to the count

    MatrixInfo* = object
        ## Info about a known matrix (square output array) for matrix_element detection
        arrayName*: string
        numRows*, numCols*: int
        elements*: seq[ArrayElement[int]]  # flat row-major array of ArrayElements

    GeostConversion* = object
        ## A detected pattern where multiple fzn_regular constraints over the same
        ## variable array encode tile placements, convertible to a single geost constraint.
        boardArrayName*: string           # FZN array name for board variables
        boardPositions*: seq[int]         # system positions for board vars
        tileVarPositions*: seq[int]       # system positions for tile placement vars
        allPlacements*: seq[seq[seq[int]]]  # cellsByPlacement[tile][idx] = cell indices
        tileValues*: seq[int]             # board value for each tile (1-indexed)
        sentinelBoardIndices*: seq[int]   # board array indices that are sentinels
        sentinelValue*: int               # sentinel value (ntiles+1)

    CaseAnalysisDef* = object
        ## A detected case-analysis channel: target variable fully determined by
        ## source variables via exhaustive bool_clause case analysis.
        targetVarName*: string
        sourceVarNames*: seq[string]     # ultimate source variable names (search positions)
        lookupTable*: seq[int]           # flat constant lookup table
        domainOffsets*: seq[int]         # min value per source (for index computation)
        domainSizes*: seq[int]          # domain size per source (hi - lo + 1)

    NoOverlapEndpoint* = object
        ## An endpoint in a NoOverlap pattern — either a constant or a variable name
        isFixed*: bool
        fixedValue*: int
        varName*: string

    NoOverlapPattern* = object
        ## A detected NoOverlap pattern: 6-literal bool_clause encoding 3D box non-overlap
        nodeA*: array[3, NoOverlapEndpoint]
        nodeB*: array[3, NoOverlapEndpoint]
        radius*: int
        boxLower*: array[3, int]
        boxUpper*: array[3, int]
        consumedConstraints*: seq[int]
        consumedBoolVars*: seq[string]

    SetVarInfo* = object
        positions*: seq[int]  # boolean variable positions in ConstraintSystem
        lo*: int              # min element of universe
        hi*: int              # max element of universe

    SetArrayElement* = object
        isConstant*: bool
        constantValues*: seq[int]  # for literal set elements
        varName*: string           # FZN name (for variable elements)

    SetUnionChainInfo* = object
        resultName*: string              # final result set variable
        baseName*: string                # base set (first arg of first union)
        baseIsConst*: bool               # true if base is a constant set
        baseConstVals*: HashSet[int]      # constant values if baseIsConst
        leafNames*: seq[string]          # leaf set names (second arg of each union)
        intermediateNames*: seq[string]  # intermediate set names (results of all but last union)
        constraintIndices*: seq[int]     # union constraint indices in chain order

    SetComprehensionPair* = object
        sumVal*: int            # ai + bi (the value this pair contributes when active)
        productVarName*: string # the int_times product variable name (expression = AND of membership)

    SetComprehensionInfo* = object
        chainIdx*: int                       # index into setUnionChains
        pairs*: seq[SetComprehensionPair]    # contributing pairs with their sum values
        consumedConstraints*: PackedSet[int] # set_in + set_card constraint indices for singletons

    SkillAllocationDef* = object
        ## A detected skill-allocation disjunctive pattern:
        ## bool_clause([b_set_in, b_and_1, ..., b_and_N], []) where:
        ##   b_set_in <- set_in_reif(alloc_var, POSENGS, b)
        ##   b_and_k  <- array_bool_and([b_skill_k, b_alloc_k], b_and_k)
        ##   b_skill_k <- int_eq_reif(new_skills_var, required_skill, b)
        ##   b_alloc_k <- int_eq_reif(alloc_var, eng_val, b)
        allocVarName*: string          # the allocation decision variable
        requiredSkill*: int            # skill value required by this job
        posEngs*: seq[int]             # engineers who already have the skill (POSENGS set)
        sortedEngs*: seq[int]          # actual engineer values in sorted order
        nsVarNames*: seq[seq[string]]  # new_skills var names per training slot
                                       # nsVarNames[t] = [ns_var for engineer 1, ..., ns_var for engineer E]
        nTrainingSlots*: int           # number of training slots

    AtMostThroughReifDef* = object
        ## A detected atMost-through-reification pattern:
        ## int_lin_le([1,...,1], [b_1,...,b_n], rhs) where each b_k comes from
        ## int_eq_reif(x_k, same_value, b_k) — counts how many x_k == same_value.
        ## Equivalent to atMost(x_positions, same_value, rhs).
        srcVarNames*: seq[string]      # the source variable names from int_eq_reif
        targetValue*: int              # the shared constant value being counted
        maxCount*: int                 # maximum allowed count (rhs)

    ArgmaxPattern* = object
        ## A detected argmax decomposition pattern:
        ## N int_ne_reif(tower, t, ne_t) + N int_lin_le_reif(coeffs, [max_var, ...], rhs, ne_t)
        ## + array_int_maximum(max_var, signal_array)
        ## Replaced by a single element constraint: signal_array[tower-1] == max_var
        towerVarName*: string         # argmax result (search variable)
        maxVarName*: string           # max(signals) channel variable
        signalVarNames*: seq[string]  # signal array elements (ordered by tower index 1..N)

    MaxFromLinLeDef* = object
        ## A detected max-from-lin-le pattern:
        ## Multiple int_lin_le([1,-1], [source, ceiling], -offset) encode ceiling >= source + offset.
        ## When the ceiling variable is minimized, it equals max(source_i + offset_i).
        ceilingVarName*: string         # the ceiling (max) variable
        sourceVarNames*: seq[string]    # source variable names
        offsets*: seq[int]              # per-source offsets
        consumedCIs*: seq[int]          # consumed constraint indices

    SpreadPatternDef* = object
        ## A detected spread pattern:
        ## Pairwise int_lin_le([1,-1,-1], [y_i, y_j, S], c) encode S >= (y_i + offset_i) - (y_j + offset_j).
        ## Replaced by max/min channels + 1 simple constraint per group.
        spreadVarName*: string          # the spread variable
        sourceVarNames*: seq[string]    # source variable names
        offsets*: seq[int]              # per-source offsets
        consumedCIs*: seq[int]          # consumed constraint indices

    DisjunctiveClauseTerm* = object
        coeffs*: seq[int]
        varNames*: seq[string]
        rhs*: int

    DisjunctiveClause* = object
        ## Each disjunct is a seq of terms (conjunction of linear inequalities).
        ## Satisfied when at least one disjunct has all its terms satisfied.
        disjuncts*: seq[seq[DisjunctiveClauseTerm]]

    ValueSupportDef* = object
        ## A detected value-support pattern: if cell has value N>1, neighbours must include 1..N-1.
        cellVarName*: string
        neighbourVarNames*: seq[string]
        maxVal*: int
        consumedCIs*: seq[int]

    FznTranslator* = object
        sys*: ConstraintSystem[int]
        # Maps FZN variable name -> position in the ConstrainedArray
        varPositions*: Table[string, int]
        # Maps FZN parameter name -> constant int value
        paramValues*: Table[string, int]
        # Maps FZN array name -> list of positions (for variable arrays) or sentinel
        arrayPositions*: Table[string, seq[int]]
        # Maps FZN array name -> constant int values (for parameter arrays)
        arrayValues*: Table[string, seq[int]]
        # Tracks which variables have output_var annotation
        outputVars*: seq[string]
        # Tracks which arrays have output_array annotation, with their index ranges
        outputArrays*: seq[tuple[name: string, lo, hi: int]]
        # The model
        model*: FznModel
        # Objective expression position (for minimize/maximize)
        objectivePos*: int
        # Direct objective expression (for defined-variable objectives, avoids indirection)
        objectiveDefExpr*: AlgebraicExpression[int]
        # Domain bounds on objective variable (deferred to optimizer, not added as hard constraints)
        objectiveLoBound*: int
        objectiveHiBound*: int
        # Set of variable names that will be replaced by defining expressions
        definedVarNames*: HashSet[string]
        # Maps defined variable name -> defining AlgebraicExpression (for defines_var elimination)
        definedVarExprs*: Table[string, AlgebraicExpression[int]]
        # Set of constraint indices that are defining constraints (to skip during translation)
        definingConstraints*: PackedSet[int]
        # Maps array name -> element variable names (for resolving defined vars in arrays)
        arrayElementNames*: Table[string, seq[string]]
        # Detected count_eq patterns (mapped by int_lin_eq constraint index)
        countEqPatterns*: Table[int, CountEqPattern]
        # Detected conditional count_eq patterns (mapped by int_lin_eq constraint index)
        conditionalCountEqPatterns*: Table[int, ConditionalCountEqPattern]
        # Geost conversion (active if tileValues.len > 0)
        geostConversion*: GeostConversion
        # Matrix infos for matrix_element pattern detection
        matrixInfos*: Table[string, MatrixInfo]
        # Domain bounds for defined variables (lo, hi) — used to add domain constraints on their expressions
        definedVarBounds*: Table[string, (int, int)]
        # Channel variable names (element defines_var outputs that should be computed, not searched)
        channelVarNames*: HashSet[string]
        # Maps constraint index -> channel var name for element constraints with defines_var
        channelConstraints*: Table[int, string]
        # Set of constraint indices that are redundant ordering constraints (transitively implied)
        redundantOrderings*: PackedSet[int]
        # Reification channel patterns: constraint index for int_eq_reif/bool2int with defines_var
        reifChannelDefs*: seq[int]      # int_eq_reif constraint indices (ordered first)
        bool2intChannelDefs*: seq[int]  # bool2int constraint indices (ordered after reif)
        leReifChannelDefs*: seq[int]    # int_le_reif/int_lt_reif channel constraint indices
        linLeReifChannelDefs*: seq[int] # int_lin_le_reif channel constraint indices
        linEqReifChannelDefs*: seq[int] # int_lin_eq_reif channel constraint indices
        # Detected implication table patterns: (condVar, targetVar) -> allowed tuples
        implicationTables*: seq[tuple[condVar, targetVar: string, tuples: seq[seq[int]]]]
        # One-hot channel defs: indicator vars to convert to channels of integer vars
        oneHotChannelDefs*: seq[tuple[indicatorVar, intVar: string, value: int]]
        # Boundary B vars that are always 0 (from int_eq_reif(bVar, 1, false))
        constantZeroChannels*: seq[string]
        # Disjunctive pair patterns: bool_clause([b1,b2],[]) where b1,b2 come from int_lin_le_reif
        disjunctivePairs*: seq[tuple[
            coeffs1: seq[int], varNames1: seq[string], rhs1: int,
            coeffs2: seq[int], varNames2: seq[string], rhs2: int]]
        # Generalized disjunctive clauses (3+ literal bool_clause and AND-of-reif patterns)
        disjunctiveClauses*: seq[DisjunctiveClause]
        # Synthetic relaxation constraints from product decomposition (for bounds propagation)
        syntheticRelaxations*: seq[DisjunctiveClauseTerm]
        # Min/max channel defs: array_int_minimum/maximum with defines_var → channel variables
        minMaxChannelDefs*: seq[tuple[ci: int, varName: string, isMin: bool]]
        # Case-analysis channel defs: bool_clause case analysis → constant lookup channel
        caseAnalysisDefs*: seq[CaseAnalysisDef]
        # bool_not with defines_var → channel variables (b = 1 - a)
        boolNotChannelDefs*: seq[int]
        # bool_clause_reif with defines_var → channel variables
        boolClauseReifChannelDefs*: seq[int]
        # set_in_reif with defines_var → channel variables
        setInReifChannelDefs*: seq[int]
        # array_bool_and/array_bool_or with defines_var → channel variables
        boolAndOrChannelDefs*: seq[int]
        # Overlap channel defs: overlap = NOT sep via bool_not chain
        overlapChannelDefs*: seq[tuple[ci: int, overlapVar: string, sepVar: string]]
        # Consumed disjunctive pair indices (replaced by cumulative constraints)
        consumedDisjunctivePairs*: PackedSet[int]
        # Detected disjunctive resource groups (cliques of disjunctive pairs → cumulative)
        disjunctiveResourceGroups*: seq[tuple[varNames: seq[string], durations: seq[int]]]
        # Detected NoOverlap patterns (6-literal bool_clause → 3D box non-overlap)
        noOverlapPatterns*: seq[NoOverlapPattern]
        # Detected inverse channel patterns: element(person[p], seat, p) groups
        inverseChannelPatterns*: seq[tuple[arrayName: string, elementCIs: seq[int],
                                                                             indexVarNames: seq[string], resultValues: seq[int],
                                                                             gccCIs: seq[int]]]
        # Indices into inverseChannelPatterns to suppress (mutual inverse secondary patterns)
        suppressedInversePatterns*: HashSet[int]
        # Tracks which output variables/arrays are boolean (for true/false formatting)
        outputBoolVars*: HashSet[string]
        outputBoolArrays*: HashSet[string]
        # Element channel aliases: maps duplicate channel var name → original channel var name
        # (when multiple element constraints share same index var and constant array)
        elementChannelAliases*: Table[string, string]
        # Maps constant-element channel var name -> (upstream index var name, constant lookup array)
        # For composing downstream bindings to skip intermediate channel variables.
        constElementSources*: Table[string, tuple[indexVar: string, constArray: seq[int]]]
        # Equality copy aliases: maps eliminated copy var name → original var name
        equalityCopyAliases*: Table[string, string]
        # Constraint indices of int_eq_reif that are equality copies (skip in buildReifChannelBindings)
        equalityCopyReifCIs*: PackedSet[int]
        # Set variable decomposition: maps FZN set var name -> boolean positions + universe bounds
        setVarBoolPositions*: Table[string, SetVarInfo]
        # Set parameter values: maps FZN set param name -> set of int values
        setParamValues*: Table[string, seq[int]]
        # Set array parameter values: maps FZN array name -> per-element set values
        setArrayValues*: Table[string, seq[seq[int]]]
        # Set array decompositions: maps FZN array name -> per-element set array info
        setArrayDecompositions*: Table[string, seq[SetArrayElement]]
        # Output set variables (for set output formatting)
        outputSetVars*: HashSet[string]
        # Output set arrays (for set array output formatting)
        outputSetArrays*: HashSet[string]
        # set_union channel defs: constraint index + result var name (non-chain unions only)
        setUnionChannelDefs*: seq[tuple[ci: int, resultName: string]]
        # Detected set_union chains (linear sequences of set_union :: defines_var)
        setUnionChains*: seq[SetUnionChainInfo]
        # Detected set comprehension patterns (chains with traced singleton→product mapping)
        setComprehensions*: seq[SetComprehensionInfo]
        # Set variable names to skip boolean creation for (singletons + intermediates)
        skipSetVarNames*: HashSet[string]
        # Index from variable name -> declaration index for O(1) lookupVarDomain
        varDomainIndex*: Table[string, int]
        # Presolve-tightened domains: applied during translateVariables, not during pattern detection
        presolveDomains*: Table[string, seq[int]]
        # Synthetic element channels: precomputed lookup tables for conditional gain variables
        syntheticElementChannels*: seq[tuple[varName: string, originVar: string, lookupTable: seq[int]]]
        # int_mod channel defs: Z = X mod C implemented as element channel with lookup table
        intModChannelDefs*: seq[tuple[varName: string, originVar: string, lookupTable: seq[int], offset: int]]
        # Singleton set channel defs: set_card(S,1) + set_in(x, S) → S.bools = indicator(x)
        singletonSetChannelDefs*: seq[tuple[setName: string, xVarName: string, cardCI: int, inCI: int]]
        # Detected weighted same-value pattern for objective
        weightedSameValuePairs*: seq[tuple[varNameA, varNameB: string, coeff: int]]
        weightedSameValueConstant*: int
        weightedSameValueObjName*: string
        weightedSameValueExpr*: WeightedSameValueExpression[int]
        # Detected conditional no-overlap pair patterns
        conditionalNoOverlapInfos*: seq[tuple[
            startAName, startBName: string,
            durationA, durationB: int,
            resourceAName, resourceBName: string,
            resourceAFixed, resourceBFixed: int,
            condAName, condBName: string,
            consumedCIs: seq[int],
            consumedVars: seq[string]]]
        # Detected conditional cumulative patterns (room_admission elimination)
        conditionalCumulativeInfos*: seq[tuple[
            fixedTasks: seq[tuple[start, duration, height: int]],
            conditionalTasks: seq[tuple[admissionVarName, selectionVarName, roomVarName: string,
                                                                     duration, height, roomValue, fixedAdmission: int]],
            limit: int,
            cumulativeCi: int,
            consumedElementCIs: seq[int],
            consumedEqReifCIs: seq[int],
            consumedBoolClauseCIs: seq[int],
            consumedRaVarNames: seq[string],
            consumedBoolVarNames: seq[string]]]
        # Detected conditional day capacity patterns (H3/H4 surgeon/OT capacity)
        conditionalDayCapacityInfos*: seq[tuple[
            tasks: seq[tuple[weight: int, admissionVarName, selectionVarName: string,
                                                extraCondVarName: string, extraCondVal: int,
                                                isMandatory: bool]],
            capacities: seq[int],
            maxDay: int,
            consumedCIs: seq[int],
            consumedVarNames: seq[string]]]
        # Detected skill-allocation disjunctive patterns (bool_clause + set_in_reif + int_eq_reif + array_bool_and)
        skillAllocationDefs*: seq[SkillAllocationDef]
        # Detected atMost-through-reification patterns (int_lin_le on int_eq_reif outputs)
        atMostThroughReifDefs*: seq[AtMostThroughReifDef]
        # Detected argmax patterns (int_ne_reif + int_lin_le_reif + array_int_maximum → element)
        argmaxPatterns*: Table[int, ArgmaxPattern]
        # Rescued defined vars: originally defined-var-only, but appear in var-indexed arrays
        # so need positions. Converted to channel variables with single-input MinMaxChannelBindings.
        rescuedChannelDefs*: seq[tuple[ci: int, varName: string]]
        # Detected max-from-lin-le patterns (int_lin_le encoding ceiling >= source + offset)
        maxFromLinLeDefs*: seq[MaxFromLinLeDef]
        # Detected spread patterns (pairwise int_lin_le → max/min channels + simple constraint)
        spreadPatternDefs*: seq[SpreadPatternDef]
        # Detected bool AND channel defs: bool_clause([b],[c1,...,cn]) where all ci are channels
        # and b appears as positive literal in exactly one bool_clause. b = AND(c1,...,cn).
        boolAndChannelDefs*: seq[tuple[ci: int, resultVar: string, condVars: seq[string]]]
        # Binary conditional channel defs: Z = element(cond, [valWhen0, valWhen1])
        # Detected from complementary bool_clause([eq_reif(Z, X)], [lt_reif]) patterns.
        binaryCondChannelDefs*: seq[tuple[targetVar: string, condChannel: string, val0Var: string, val1Var: string, consumedCIs: seq[int]]]
        # One-hot conditional channel defs: Z = element(weightedIndex, constTable)
        # Detected from exhaustive bool_clause([eq_reif(Z, v_i)], [eq_reif(X_i, c)]) patterns.
        oneHotCondChannelDefs*: seq[tuple[targetVar: string, condChannels: seq[string], targetVals: seq[int], consumedCIs: seq[int]]]
        # Detected value-support patterns (bool_clause + int_eq_reif + int_le_reif → native constraint)
        valueSupportDefs*: seq[ValueSupportDef]
        # Bool vars consumed by value-support detection (skip in channel detection)
        valueSupportConsumedBools*: HashSet[string]
        # Net flow pair detection (EFM / metabolic network patterns)
        netFlowPairInVar*: seq[string]     # pair index → V_in name
        netFlowPairOutVar*: seq[string]    # pair index → V_out name
        netFlowFreePairs*: seq[int]        # free pair indices (search variables)
        netFlowDependentPairs*: seq[int]   # dependent pair indices (channels, in topo order)
        netFlowDepTerms*: seq[seq[tuple[pairId: int, coeff: int]]]  # dependency terms per dependent pair
        netFlowDomainBound*: int           # flux domain upper bound (e.g., 50)
        # Multi-resource no-overlap pair infos: groups of bool_clause([], [assign_i_r, assign_j_r, overlap_u])
        multiResourceNoOverlapInfos*: seq[tuple[
            overlapVarName: string,
            assignPairNames: seq[(string, string)],  # (assign[i,r], assign[j,r]) per resource
            consumedCIs: seq[int]]]
        # Bool_xor negation defs: bool_xor(const, var, result) where const=true → result = 1-var
        boolXorNegDefs*: seq[tuple[inputArg: FznExpr, resultVar: string]]
        # Bool equivalence alias defs: mutual bool_clause implications → alias channels
        boolEquivAliasDefs*: seq[tuple[aliasVar, canonicalVar: string, consumedCIs: seq[int]]]
        # Bool-gated variable channel defs: x = if cond then y else constant
        boolGatedVarChannelDefs*: seq[tuple[targetVar, condVar, valVar: string, constValue: int, consumedCIs: seq[int]]]

proc getExpr*(tr: FznTranslator, pos: int): AlgebraicExpression[int] {.inline.} =
    tr.sys.baseArray[pos]

proc resolveExprArg*(tr: FznTranslator, arg: FznExpr): AlgebraicExpression[int] =
    ## Resolves a FznExpr to an AlgebraicExpression.
    ## For identifiers: looks up variable position, or returns defining expression for defined vars.
    ## For int literals: creates a literal expression with no positions.
    ## For bool literals: true=1, false=0.
    case arg.kind
    of FznIdent:
        if arg.ident in tr.definedVarExprs:
            return tr.definedVarExprs[arg.ident]
        elif arg.ident in tr.varPositions:
            return tr.getExpr(tr.varPositions[arg.ident])
        elif arg.ident in tr.paramValues:
            let val = tr.paramValues[arg.ident]
            return newAlgebraicExpression[int](
                positions = initPackedSet[int](),
                node = ExpressionNode[int](kind: LiteralNode, value: val),
                linear = true
            )
        else:
            raise newException(KeyError, &"Unknown identifier '{arg.ident}' in expression")
    of FznIntLit:
        return newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: arg.intVal),
            linear = true
        )
    of FznBoolLit:
        let val = if arg.boolVal: 1 else: 0
        return newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: val),
            linear = true
        )
    else:
        raise newException(ValueError, &"Cannot resolve {arg.kind} as expression")

proc resolveIntArg*(tr: FznTranslator, arg: FznExpr): int =
    ## Resolves a FznExpr that must be a constant integer.
    case arg.kind
    of FznIntLit:
        return arg.intVal
    of FznBoolLit:
        return if arg.boolVal: 1 else: 0
    of FznIdent:
        if arg.ident in tr.paramValues:
            return tr.paramValues[arg.ident]
        else:
            raise newException(KeyError, &"Expected constant, got variable '{arg.ident}'")
    else:
        raise newException(ValueError, &"Expected int constant, got {arg.kind}")

proc resolveIntArray*(tr: FznTranslator, arg: FznExpr): seq[int] =
    ## Resolves a FznExpr to a constant int array.
    case arg.kind
    of FznArrayLit:
        result = newSeq[int](arg.elems.len)
        for i, e in arg.elems:
            result[i] = tr.resolveIntArg(e)
    of FznIdent:
        if arg.ident in tr.arrayValues:
            return tr.arrayValues[arg.ident]
        else:
            raise newException(KeyError, &"Unknown constant array '{arg.ident}'")
    else:
        raise newException(ValueError, &"Expected array, got {arg.kind}")

proc resolveExprArray*(tr: FznTranslator, arg: FznExpr): seq[AlgebraicExpression[int]] =
    ## Resolves a FznExpr to an array of AlgebraicExpressions (for variable arrays).
    case arg.kind
    of FznArrayLit:
        result = newSeq[AlgebraicExpression[int]](arg.elems.len)
        for i, e in arg.elems:
            result[i] = tr.resolveExprArg(e)
    of FznIdent:
        if arg.ident in tr.arrayPositions:
            let positions = tr.arrayPositions[arg.ident]
            result = newSeq[AlgebraicExpression[int]](positions.len)
            for i, pos in positions:
                if pos == -1:
                    # Defined variable - use defining expression
                    if arg.ident in tr.arrayElementNames:
                        let elemName = tr.arrayElementNames[arg.ident][i]
                        if elemName in tr.definedVarExprs:
                            result[i] = tr.definedVarExprs[elemName]
                            continue
                    raise newException(ValueError, &"Array '{arg.ident}' element {i} has no position or defining expression")
                result[i] = tr.getExpr(pos)
        elif arg.ident in tr.arrayValues:
            # Constant array - create literal expressions
            let vals = tr.arrayValues[arg.ident]
            result = newSeq[AlgebraicExpression[int]](vals.len)
            for i, v in vals:
                result[i] = newAlgebraicExpression[int](
                    positions = initPackedSet[int](),
                    node = ExpressionNode[int](kind: LiteralNode, value: v),
                    linear = true
                )
        else:
            raise newException(KeyError, &"Unknown array '{arg.ident}'")
    else:
        raise newException(ValueError, &"Expected array, got {arg.kind}")

proc resolvePositionArray*(tr: FznTranslator, arg: FznExpr): seq[int] =
    ## Resolves a FznExpr to positions (for constraints that take position arrays).
    case arg.kind
    of FznArrayLit:
        result = newSeq[int](arg.elems.len)
        for i, e in arg.elems:
            case e.kind
            of FznIdent:
                if e.ident in tr.varPositions:
                    result[i] = tr.varPositions[e.ident]
                else:
                    raise newException(KeyError, &"Unknown variable '{e.ident}'")
            else:
                raise newException(ValueError, &"Expected variable identifier, got {e.kind}")
    of FznIdent:
        if arg.ident in tr.arrayPositions:
            return tr.arrayPositions[arg.ident]
        else:
            raise newException(KeyError, &"Unknown variable array '{arg.ident}'")
    else:
        raise newException(ValueError, &"Expected array of variables, got {arg.kind}")

proc resolveMixedArray*(tr: FznTranslator, arg: FznExpr): seq[ArrayElement[int]] =
    ## Resolves a FznExpr to a mixed constant/variable array (for element constraints).
    case arg.kind
    of FznArrayLit:
        result = newSeq[ArrayElement[int]](arg.elems.len)
        for i, e in arg.elems:
            case e.kind
            of FznIdent:
                if e.ident in tr.varPositions:
                    result[i] = ArrayElement[int](isConstant: false, variablePosition: tr.varPositions[e.ident])
                elif e.ident in tr.paramValues:
                    result[i] = ArrayElement[int](isConstant: true, constantValue: tr.paramValues[e.ident])
                else:
                    raise newException(KeyError, &"Unknown identifier '{e.ident}'")
            of FznIntLit:
                result[i] = ArrayElement[int](isConstant: true, constantValue: e.intVal)
            of FznBoolLit:
                result[i] = ArrayElement[int](isConstant: true, constantValue: if e.boolVal: 1 else: 0)
            else:
                raise newException(ValueError, &"Expected variable or constant, got {e.kind}")
    of FznIdent:
        if arg.ident in tr.arrayPositions:
            let positions = tr.arrayPositions[arg.ident]
            result = newSeq[ArrayElement[int]](positions.len)
            for i, pos in positions:
                if pos == -1:
                    # Defined variable - treat as constant if we can resolve it
                    if arg.ident in tr.arrayElementNames:
                        let elemName = tr.arrayElementNames[arg.ident][i]
                        if elemName in tr.paramValues:
                            result[i] = ArrayElement[int](isConstant: true, constantValue: tr.paramValues[elemName])
                            continue
                    raise newException(ValueError, &"Array '{arg.ident}' element {i} has no position or constant value")
                let dom = tr.sys.baseArray.domain[pos]
                if dom.len == 1:
                    result[i] = ArrayElement[int](isConstant: true, constantValue: dom[0])
                else:
                    result[i] = ArrayElement[int](isConstant: false, variablePosition: pos)
        elif arg.ident in tr.arrayValues:
            let vals = tr.arrayValues[arg.ident]
            result = newSeq[ArrayElement[int]](vals.len)
            for i, v in vals:
                result[i] = ArrayElement[int](isConstant: true, constantValue: v)
        else:
            raise newException(KeyError, &"Unknown array '{arg.ident}'")
    else:
        raise newException(ValueError, &"Expected array literal, got {arg.kind}")


proc buildMatrixInfos(tr: var FznTranslator) =
        ## Builds MatrixInfo entries for output arrays that are perfect squares.
        ## These enable matrix_element pattern detection in element constraint translation.
        for oa in tr.outputArrays:
                let name = oa.name
                if name notin tr.arrayPositions:
                        continue
                let positions = tr.arrayPositions[name]
                let size = positions.len
                # Check for perfect square
                let n = int(float(size).sqrt + 0.5)
                if n * n != size:
                        continue
                # Build elements array — skip arrays containing defined variables (pos == -1)
                # since they don't have real positions and can't be used for matrix element constraints
                var elements = newSeq[ArrayElement[int]](size)
                var hasDefinedVar = false
                for i in 0..<size:
                        let pos = positions[i]
                        if pos == -1:
                                hasDefinedVar = true
                                break
                        let dom = tr.sys.baseArray.domain[pos]
                        if dom.len == 1:
                                elements[i] = ArrayElement[int](isConstant: true, constantValue: dom[0])
                        else:
                                elements[i] = ArrayElement[int](isConstant: false, variablePosition: pos)
                if hasDefinedVar:
                        continue
                tr.matrixInfos[name] = MatrixInfo(
                        arrayName: name,
                        numRows: n,
                        numCols: n,
                        elements: elements
                )


proc matchMatrixRow(tr: FznTranslator, inlineElems: seq[ArrayElement[int]],
                                         matrixInfo: MatrixInfo): int =
        ## Checks if inlineElems matches a specific row of the matrix.
        ## Returns the row index if matched, -1 otherwise.
        let numCols = matrixInfo.numCols
        if inlineElems.len != numCols:
                return -1
        for r in 0..<matrixInfo.numRows:
                var matches = true
                for c in 0..<numCols:
                        let flatIdx = r * numCols + c
                        let me = matrixInfo.elements[flatIdx]
                        let ie = inlineElems[c]
                        if me.isConstant and ie.isConstant:
                                if me.constantValue != ie.constantValue:
                                        matches = false
                                        break
                        elif not me.isConstant and not ie.isConstant:
                                if me.variablePosition != ie.variablePosition:
                                        matches = false
                                        break
                        else:
                                matches = false
                                break
                if matches:
                        return r
        return -1

proc matchMatrixCol(tr: FznTranslator, inlineElems: seq[ArrayElement[int]],
                                         matrixInfo: MatrixInfo): int =
        ## Checks if inlineElems matches a specific column of the matrix.
        ## Returns the column index if matched, -1 otherwise.
        let numRows = matrixInfo.numRows
        let numCols = matrixInfo.numCols
        if inlineElems.len != numRows:
                return -1
        for c in 0..<numCols:
                var matches = true
                for r in 0..<numRows:
                        let flatIdx = r * numCols + c
                        let me = matrixInfo.elements[flatIdx]
                        let ie = inlineElems[r]
                        if me.isConstant and ie.isConstant:
                                if me.constantValue != ie.constantValue:
                                        matches = false
                                        break
                        elif not me.isConstant and not ie.isConstant:
                                if me.variablePosition != ie.variablePosition:
                                        matches = false
                                        break
                        else:
                                matches = false
                                break
                if matches:
                        return c
        return -1

proc stripSolverPrefix(name: string): string =
    ## Strips solver-specific prefixes like gecode_, chuffed_ and maps to fzn_ equivalents.
    for prefix in ["gecode_", "chuffed_", "sicstus_"]:
        if name.startsWith(prefix):
            let stripped = name[prefix.len..^1]
            # Some gecode names need remapping
            if stripped == "all_different_int":
                return "fzn_all_different_int"
            elif stripped == "cumulatives":
                return "fzn_cumulative"
            return "fzn_" & stripped
    return name

proc extractSetValues(value: FznExpr): seq[int] =
    ## Extract integer values from a set literal or range expression.
    case value.kind
    of FznSetLit:
        return value.setElems
    of FznRange:
        if value.lo > value.hi:
            return @[]  # empty set (e.g., 1..0)
        return toSeq(value.lo..value.hi)
    else:
        return @[]

include translatorCore
include translatorPresolve
include translatorDefinedVars
include translatorChannels
include translatorPatterns
include translatorScheduling

proc translate*(model: FznModel): FznTranslator =
    ## Translates a complete FznModel to a ConstraintSystem.
    result.sys = initConstraintSystem[int]()
    result.model = model
    result.varPositions = initTable[string, int]()
    result.paramValues = initTable[string, int]()
    result.arrayPositions = initTable[string, seq[int]]()
    result.arrayValues = initTable[string, seq[int]]()
    result.definedVarNames = initHashSet[string]()
    result.definedVarExprs = initTable[string, AlgebraicExpression[int]]()
    result.arrayElementNames = initTable[string, seq[string]]()
    result.countEqPatterns = initTable[int, CountEqPattern]()
    result.conditionalCountEqPatterns = initTable[int, ConditionalCountEqPattern]()
    result.argmaxPatterns = initTable[int, ArgmaxPattern]()
    result.matrixInfos = initTable[string, MatrixInfo]()
    result.definedVarBounds = initTable[string, (int, int)]()
    result.channelVarNames = initHashSet[string]()
    result.channelConstraints = initTable[int, string]()
    result.objectivePos = ObjPosNone
    result.objectiveLoBound = low(int)
    result.objectiveHiBound = high(int)
    result.elementChannelAliases = initTable[string, string]()
    result.constElementSources = initTable[string, tuple[indexVar: string, constArray: seq[int]]]()
    result.equalityCopyAliases = initTable[string, string]()
    result.equalityCopyReifCIs = initPackedSet[int]()
    result.setVarBoolPositions = initTable[string, SetVarInfo]()
    result.setParamValues = initTable[string, seq[int]]()
    result.setArrayValues = initTable[string, seq[seq[int]]]()
    result.setArrayDecompositions = initTable[string, seq[SetArrayElement]]()
    result.outputSetVars = initHashSet[string]()
    result.outputSetArrays = initHashSet[string]()
    result.skipSetVarNames = initHashSet[string]()
    result.rescuedChannelDefs = @[]
    result.boolAndChannelDefs = @[]
    result.binaryCondChannelDefs = @[]
    result.oneHotCondChannelDefs = @[]
    result.boolEquivAliasDefs = @[]
    result.boolGatedVarChannelDefs = @[]

    # Load parameters first (needed by collectDefinedVars for resolveIntArray)
    result.translateParameters()
    # Presolve: fixpoint propagation to fix singletons, tighten domains, eliminate constraints
    result.presolve()
    # Collect defined variables before translating variables
    result.collectDefinedVars()
    # Detect net flow pairs (EFM / metabolic network: paired vars with tree-structured constraints)
    # MUST run before other detection to consume stoichiometry + reversibility constraints early
    result.detectNetFlowPairs()
    # Detect int_mod channel patterns (Z = X mod C → element channel)
    result.detectIntModChannels()
    # Detect conditional count_eq patterns (int_lin_eq → bool2int → array_bool_and → int_eq_reif × 2)
    result.detectConditionalCountPatterns()
    # Detect count_eq patterns before translating variables (marks intermediate vars as defined)
    result.detectCountPatterns()
    # Detect max-from-lin-le patterns (ceiling >= source + offset → max channel)
    result.detectMaxFromLinLe()
    # NOTE: detectSpreadPattern is intentionally NOT called here.
    # It removes pairwise int_lin_le constraints that provide useful gradient information
    # for tabu search. The max/min channel replacement loses per-pair penalty signals.
    # Detect weighted same-value objective pattern (Σ coeff_k * δ(x_i == x_j) + constant)
    result.detectWeightedSameValuePattern()
    # Detect value-support patterns (bool_clause + int_eq_reif + int_le_reif → native constraint)
    # MUST run before detectReifChannels to prevent consumed booleans from being channeled
    result.detectValueSupportPattern()
    # Detect skill-allocation disjunctive patterns (MUST run before detectReifChannels
    # to prevent intermediate booleans from being wastefully channeled)
    result.detectSkillAllocationPattern()
    # Detect atMost-through-reification: int_lin_le([1,...,1], [int_eq_reif outputs]) → direct atMost
    # (MUST run after skill-allocation detection and before detectReifChannels)
    result.detectAtMostThroughReif()
    # Detect disjunctive pair patterns (bool_clause + int_lin_le_reif)
    # MUST run before detectReifChannels so int_lin_le_reif channelization doesn't consume these
    result.detectDisjunctivePairs()
    # Detect small-domain product patterns (int_times with small operand → case-split)
    result.detectSmallDomainProducts()
    # Detect disjunctive resource groups (cliques of pairs → cumulative)
    result.detectDisjunctiveResources()
    # Fold bool_xor constraints with constant inputs (before reif channel detection)
    result.detectBoolXorSimplification()
    # Detect int_eq_reif/bool2int defines_var patterns → channel variables
    result.detectReifChannels()
    # Detect bool AND channels: bool_clause([b],[c1,...,cn]) where all ci are channels
    # MUST run after detectReifChannels() so channelVarNames is populated with reif channels
    result.detectBoolAndChannels()
    # Detect bool equivalence alias channels: mutual bool_clause implications → alias
    # MUST run after detectBoolAndChannels() so channelVarNames includes AND channels.
    # Run as fixpoint since new aliases may enable further equivalences.
    block:
        var prevCount = -1
        var iterations = 0
        while result.boolEquivAliasDefs.len != prevCount and iterations < 10:
            prevCount = result.boolEquivAliasDefs.len
            result.detectBoolEquivalenceChannels()
            inc iterations
    # Detect overlap channels: overlap = NOT sep where sep is a bool_clause_reif channel
    # MUST run after detectReifChannels() (which populates boolNotChannelDefs)
    result.detectOverlapChannels()
    # Detect conditional implication channels: binary (min/max pair) and one-hot (permutation lookup)
    # MUST run after detectReifChannels() and detectBoolAndChannels()
    result.detectConditionalImplicationChannels()
    # Detect bool-gated variable channels: x = if cond then y else constant
    # MUST run after detectConditionalImplicationChannels() and detectBoolEquivalenceChannels()
    result.detectBoolGatedVariableChannels()
    # Detect argmax decomposition patterns (int_ne_reif + int_lin_le_reif + array_int_maximum → element)
    result.detectArgmaxPattern()
    # Detect set_union defines_var patterns → channel variables for set decomposition
    result.detectSetUnionChannels()
    # Detect equality copy variables (vars only in defines_var constraints, aliased to original)
    result.detectEqualityCopyVars()
    # Detect case-analysis channels (bool_clause exhaustive case patterns → lookup tables)
    # Run as fixpoint: first pass channels simple targets (e.g. job_time), subsequent passes
    # channel targets that depend on earlier results (e.g. job_end depending on job_time).
    block:
        var prevCount = -1
        var iterations = 0
        while result.caseAnalysisDefs.len != prevCount and iterations < 10:
            prevCount = result.caseAnalysisDefs.len
            result.detectCaseAnalysisChannels()
            inc iterations
    # Detect int_lin_eq_reif defines_var patterns → channel variables
    # MUST run after case-analysis fixpoint (which uses int_lin_eq_reif via linEqReifMap)
    result.detectLinEqReifChannels()
    # Re-run case-analysis: new int_lin_eq_reif channels may enable
    # additional case-analysis detection (e.g., alone predicate outputs)
    block:
        var prevCount = -1
        var iterations = 0
        while result.caseAnalysisDefs.len != prevCount and iterations < 10:
            prevCount = result.caseAnalysisDefs.len
            result.detectCaseAnalysisChannels()
            inc iterations
    # Detect implication-to-table and one-hot channel patterns
    result.detectImplicationPatterns()
    # Detect conditional gain patterns (reified value assignment → element channel)
    result.detectConditionalGainChannels()
    # Detect NoOverlap patterns (6-literal bool_clause → 3D box non-overlap)
    result.detectNoOverlapPatterns()
    # Detect DFA-to-geost pattern (needs paramValues for DFA data)
    result.detectDfaGeostPattern()
    # Detect conditional no-overlap pair patterns (room-conflict bool_clause chains)
    result.detectConditionalNoOverlapPairs()
    # Detect multi-resource no-overlap pairs (groups of bool_clause([], [a, b, overlap]))
    result.detectMultiResourceNoOverlapPairs()
    # Detect conditional cumulative patterns (room_admission elimination)
    result.detectConditionalCumulativePattern()
    # Detect conditional day capacity patterns (H3/H4 surgeon/OT capacity)
    result.detectConditionalDayCapacityPattern()
    # Detect redundant ordering constraints (transitive reduction)
    result.detectRedundantOrderings()
    result.translateVariables()
    # Create net flow variables and channel bindings (after translateVariables so V positions exist)
    if result.netFlowFreePairs.len > 0:
        result.buildNetFlowVariables()
    # Mark channelVarNames positions as channelPositions (for vars like ra vars
    # that are marked as channels during detection but don't have channel bindings)
    for vn in result.channelVarNames:
        if vn in result.varPositions:
            result.sys.baseArray.channelPositions.incl(result.varPositions[vn])
    # Detect singleton set channels: set_card(S,1) + set_in(x,S) → S.bools become channels
    result.detectSingletonSetChannels()
    for def in result.singletonSetChannelDefs:
        if def.setName in result.setVarBoolPositions:
            for bpos in result.setVarBoolPositions[def.setName].positions:
                result.sys.baseArray.channelPositions.incl(bpos)
    # Prune unreferenced domain values from variables in skill-allocation patterns
    if result.skillAllocationDefs.len > 0:
        result.pruneUnreferencedSkillValues()
    # Emit compact constraints for skill-allocation patterns (Phase 2 + Phase 3)
    if result.skillAllocationDefs.len > 0:
        result.emitSkillAllocationConstraints()
    # Emit direct atMost constraints for detected atMost-through-reification patterns
    if result.atMostThroughReifDefs.len > 0:
        result.emitAtMostThroughReif()
    # Build expressions for defined variables using the now-created positions
    # (must run before emitMaxFromLinLeChannels which resolves source vars as expressions)
    result.buildDefinedExpressions()
    # Build expressions for element channel aliases (duplicate → original channel's position)
    for aliasName, originalName in result.elementChannelAliases:
        if originalName in result.varPositions:
            result.definedVarExprs[aliasName] = result.getExpr(result.varPositions[originalName])
        elif originalName in result.definedVarExprs:
            result.definedVarExprs[aliasName] = result.definedVarExprs[originalName]
    # Build expressions for equality copy aliases (copy → original's expression)
    for copyName, originalName in result.equalityCopyAliases:
        if originalName in result.varPositions:
            result.definedVarExprs[copyName] = result.getExpr(result.varPositions[originalName])
        elif originalName in result.definedVarExprs:
            result.definedVarExprs[copyName] = result.definedVarExprs[originalName]
    # Emit max channels for detected max-from-lin-le patterns
    if result.maxFromLinLeDefs.len > 0:
        result.emitMaxFromLinLeChannels()
    # NOTE: emitSpreadPatternChannels intentionally not called (see detection note above)
    # Tighten domains from diffn time profile analysis
    result.tightenDiffnTimeProfile()
    # Bidirectional ceiling/source domain tightening for max-from-lin-le patterns
    result.tightenMaxFromLinLeBounds()
    # Prune admission domains using zero-capacity day detection
    result.pruneZeroCapacityDays()
    # Build set of variable names that are inputs to min/max channels.
    # Bounds on these intermediate variables are MiniZinc domain analysis artifacts,
    # not problem constraints. The min/max channel propagation maintains correct values
    # regardless of whether intermediate inputs are within their declared domains.
    var minMaxInputNames: HashSet[string]
    for def in result.minMaxChannelDefs:
        let con = result.model.constraints[def.ci]
        # Extract input array variable names
        let inputArg = con.args[1]
        case inputArg.kind
        of FznArrayLit:
            for elem in inputArg.elems:
                if elem.kind == FznIdent:
                    minMaxInputNames.incl(elem.ident)
        else:
            # Named array reference — resolve through resolveVarArrayElems
            let resolved = result.resolveVarArrayElems(inputArg)
            for elem in resolved:
                if elem.kind == FznIdent:
                    minMaxInputNames.incl(elem.ident)
    # Also add transitive inputs: if a min/max input is itself a defined variable
    # whose expression references other defined variables, those are also safe to skip
    if minMaxInputNames.len > 0:
        var changed = true
        while changed:
            changed = false
            for ci in result.definingConstraints.items:
                let con = result.model.constraints[ci]
                let name = stripSolverPrefix(con.name)
                if name != "int_lin_eq" or not con.hasAnnotation("defines_var"):
                    continue
                let ann = con.getAnnotation("defines_var")
                if ann.args.len == 0 or ann.args[0].kind != FznIdent:
                    continue
                let definedName = ann.args[0].ident
                if definedName notin minMaxInputNames:
                    continue
                # This defined variable is a min/max input — add all its dependencies too
                let varElems = result.resolveVarArrayElems(con.args[1])
                for v in varElems:
                    if v.kind == FznIdent and v.ident in result.definedVarNames and
                         v.ident notin minMaxInputNames:
                        minMaxInputNames.incl(v.ident)
                        changed = true
    # Determine objective variable name — its domain bounds are deferred to optimizer
    # rather than added as hard constraints (too tight for local search to satisfy directly)
    var objectiveVarName = ""
    if result.model.solve.kind in {Minimize, Maximize}:
        if result.model.solve.objective != nil and result.model.solve.objective.kind == FznIdent:
            objectiveVarName = result.model.solve.objective.ident

    # Add domain constraints for defined variables with finite bounds,
    # but skip bounds that are naturally satisfied by the expression's range
    # or where the variable is an input to a min/max channel (bounds are MiniZinc
    # domain artifacts, not problem constraints)
    var nBoundsSkipped = 0
    var nChannelBoundsSkipped = 0
    var nObjBoundsSkipped = 0
    for varName, bounds in result.definedVarBounds:
        if varName in result.definedVarExprs:
            let expr = result.definedVarExprs[varName]
            # Skip bounds on element channel aliases (same range as original channel)
            if varName in result.elementChannelAliases:
                nBoundsSkipped += 2
                continue
            # Skip bounds on min/max channel input variables
            if varName in minMaxInputNames:
                nChannelBoundsSkipped += 2
                continue
            # Skip bounds on objective variable — defer to optimizer for two-phase solving
            if varName == objectiveVarName:
                let (lo, hi) = bounds
                result.objectiveLoBound = lo
                result.objectiveHiBound = hi
                nObjBoundsSkipped += 2
                continue
            let (lo, hi) = bounds
            let (exprMin, exprMax) = result.estimateRange(expr.node)
            if lo > low(int) and lo > exprMin:
                result.sys.addConstraint(expr >= lo)
            else:
                inc nBoundsSkipped
            if hi < high(int) and hi < exprMax:
                result.sys.addConstraint(expr <= hi)
            else:
                inc nBoundsSkipped
    # Handle objective bounds for weighted same-value objective (not in definedVarExprs)
    if result.weightedSameValueObjName != "" and result.weightedSameValueObjName in result.definedVarBounds:
        let (lo, hi) = result.definedVarBounds[result.weightedSameValueObjName]
        result.objectiveLoBound = lo
        result.objectiveHiBound = hi
        nObjBoundsSkipped += 2
    if nBoundsSkipped > 0 or nChannelBoundsSkipped > 0 or nObjBoundsSkipped > 0:
        stderr.writeLine(&"[FZN] Skipped {nBoundsSkipped + nChannelBoundsSkipped + nObjBoundsSkipped} defined-var bounds (range={nBoundsSkipped} channel={nChannelBoundsSkipped} objective={nObjBoundsSkipped})")
    if nObjBoundsSkipped > 0:
        stderr.writeLine(&"[FZN] Objective domain bounds [{result.objectiveLoBound}..{result.objectiveHiBound}] deferred to optimizer")
    # Build matrix infos for matrix_element pattern detection
    result.buildMatrixInfos()

    # Detect involution patterns (array_var_int_element groups encoding A[A[i]]=i)
    result.detectInversePatterns()

    # Detect inverse channel patterns (element(person[p], seat, p) groups)
    result.detectInverseChannelPatterns()

    # Detect if-then-else channels (int_lin_ne_reif + int_eq_reif + bool_clause → 2D table channel)
    result.detectIfThenElseChannels()

    # Detect GCC count channels (variable-count GCC outputs → count-eq channel bindings)
    result.detectGccCountChannels()

    # If geost conversion is active, record board positions and create tile variables
    let gc = result.geostConversion
    if gc.tileValues.len > 0:
        if gc.boardArrayName in result.arrayPositions:
            result.geostConversion.boardPositions = result.arrayPositions[gc.boardArrayName]
        # Create tile placement variables
        for t in 0..<gc.tileValues.len:
            let pos = result.sys.baseArray.len
            let v = result.sys.newConstrainedVariable()
            v.setDomain(toSeq(0..<gc.allPlacements[t].len))
            result.geostConversion.tileVarPositions.add(pos)

    var nSkippedDefining, nSkippedRedundant, nTranslated = 0
    for ci, con in model.constraints:
        if ci in result.definingConstraints:
            inc nSkippedDefining
            continue
        if ci in result.redundantOrderings:
            inc nSkippedRedundant
            continue
        if ci in result.conditionalCountEqPatterns:
            # Emit conditional count_eq channel binding for detected pattern
            let pattern = result.conditionalCountEqPatterns[ci]
            proc resolveVarPos(tr: FznTranslator, vn: string): int =
                if vn in tr.varPositions:
                    return tr.varPositions[vn]
                elif vn in tr.definedVarExprs:
                    let expr = tr.definedVarExprs[vn]
                    if expr.node.kind == RefNode:
                        return expr.node.position
                raise newException(KeyError, &"Unknown/non-position var '{vn}' in conditional count_eq pattern")
            var primaryPos, filterPos, primaryOnlyPos: seq[int]
            for vn in pattern.primaryVarNames:
                primaryPos.add(result.resolveVarPos(vn))
            for vn in pattern.filterVarNames:
                filterPos.add(result.resolveVarPos(vn))
            for vn in pattern.primaryOnlyVarNames:
                primaryOnlyPos.add(result.resolveVarPos(vn))
            let targetPos = result.varPositions[pattern.targetVarName]
            result.sys.baseArray.addConditionalCountEqChannelBinding(
                targetPos, pattern.targetValue, primaryPos, filterPos,
                pattern.filterValue, primaryOnlyPos, pattern.constantOffset)
            result.channelVarNames.incl(pattern.targetVarName)
            # Set domain to channel range intersected with original declared domain
            let totalIndicators = primaryPos.len + primaryOnlyPos.len
            let channelMax = totalIndicators + pattern.constantOffset
            let channelMin = pattern.constantOffset
            let origDomain = result.sys.baseArray.domain[targetPos]
            let origMin = if origDomain.len > 0: origDomain[0] else: channelMin
            let origMax = if origDomain.len > 0: origDomain[^1] else: channelMax
            let effectiveMin = max(channelMin, origMin)
            let effectiveMax = min(channelMax, origMax)
            result.sys.baseArray.domain[targetPos] = toSeq(effectiveMin..effectiveMax)
            # Add explicit bound constraints when original domain is narrower than channel range
            if origMin > channelMin:
                result.sys.addConstraint(result.getExpr(targetPos) >= origMin)
            if origMax < channelMax:
                result.sys.addConstraint(result.getExpr(targetPos) <= origMax)
        elif ci in result.countEqPatterns:
            # Emit count_eq for detected pattern
            let pattern = result.countEqPatterns[ci]
            var arrayPos: seq[int]
            for vn in pattern.arrayVarNames:
                if vn in result.varPositions:
                    arrayPos.add(result.varPositions[vn])
                else:
                    raise newException(KeyError, &"Unknown variable '{vn}' in count_eq pattern")
            let targetPos = result.varPositions[pattern.targetVarName]
            result.sys.addConstraint(countEq[int](arrayPos, pattern.countValue, targetPos))
        elif ci in result.argmaxPatterns:
            # Emit element constraint for detected argmax pattern: signal_array[tower-1] == max_signal
            let p = result.argmaxPatterns[ci]
            let indexExpr = result.resolveExprArg(FznExpr(kind: FznIdent, ident: p.towerVarName)) - 1
            var signalExprs: seq[AlgebraicExpression[int]]
            for sn in p.signalVarNames:
                signalExprs.add(result.resolveExprArg(FznExpr(kind: FznIdent, ident: sn)))
            let maxExpr = result.resolveExprArg(FznExpr(kind: FznIdent, ident: p.maxVarName))
            result.sys.addConstraint(elementExpr(indexExpr, signalExprs, maxExpr))
        else:
            inc nTranslated
            result.translateConstraint(con)

    stderr.writeLine(&"[FZN] Constraint translation: {nSkippedDefining} skipped (defining), {nSkippedRedundant} skipped (redundant), {nTranslated} translated")

    # Add table constraints for detected implication patterns
    var nTableDomainRestrictions = 0
    for tbl in result.implicationTables:
        let condHasPos = tbl.condVar in result.varPositions
        let targetHasPos = tbl.targetVar in result.varPositions
        if condHasPos and targetHasPos:
            let condPos = result.varPositions[tbl.condVar]
            let targetPos = result.varPositions[tbl.targetVar]
            result.sys.addConstraint(tableInGacSafe[int](@[condPos, targetPos], tbl.tuples))
        elif not condHasPos and targetHasPos:
            # condVar was eliminated — check if it's a constant
            if tbl.condVar in result.definedVarExprs:
                let expr = result.definedVarExprs[tbl.condVar]
                if expr.node.kind == LiteralNode:
                    let constVal = expr.node.value
                    let targetPos = result.varPositions[tbl.targetVar]
                    # Filter tuples to those matching the constant condVar value
                    var allowed: PackedSet[int]
                    for t in tbl.tuples:
                        if t[0] == constVal:
                            allowed.incl(t[1])
                    if allowed.len > 0:
                        # Restrict targetVar's domain to intersection with allowed values
                        let currentDom = result.sys.baseArray.domain[targetPos]
                        var newDom: seq[int]
                        for v in currentDom:
                            if v in allowed:
                                newDom.add(v)
                        if newDom.len > 0 and newDom.len < currentDom.len:
                            result.sys.baseArray.setDomain(targetPos, newDom)
                            inc nTableDomainRestrictions
        elif condHasPos and not targetHasPos:
            # targetVar was eliminated — check if it's a constant
            if tbl.targetVar in result.definedVarExprs:
                let expr = result.definedVarExprs[tbl.targetVar]
                if expr.node.kind == LiteralNode:
                    let constVal = expr.node.value
                    let condPos = result.varPositions[tbl.condVar]
                    # Filter tuples to those matching the constant targetVar value
                    var allowed: PackedSet[int]
                    for t in tbl.tuples:
                        if t[1] == constVal:
                            allowed.incl(t[0])
                    if allowed.len > 0:
                        let currentDom = result.sys.baseArray.domain[condPos]
                        var newDom: seq[int]
                        for v in currentDom:
                            if v in allowed:
                                newDom.add(v)
                        if newDom.len > 0 and newDom.len < currentDom.len:
                            result.sys.baseArray.setDomain(condPos, newDom)
                            inc nTableDomainRestrictions
    if nTableDomainRestrictions > 0:
        stderr.writeLine(&"[FZN] Table domain restrictions from eliminated variables: {nTableDomainRestrictions}")

    # Add disjunctive pair constraints: min(max(0, expr1), max(0, expr2)) == 0
    for pairIdx, pair in result.disjunctivePairs:
        if pairIdx in result.consumedDisjunctivePairs:
            continue
        var exprs1 = newSeq[AlgebraicExpression[int]](pair.varNames1.len)
        for i, vn in pair.varNames1:
            exprs1[i] = result.resolveExprArg(FznExpr(kind: FznIdent, ident: vn))
        var exprs2 = newSeq[AlgebraicExpression[int]](pair.varNames2.len)
        for i, vn in pair.varNames2:
            exprs2[i] = result.resolveExprArg(FznExpr(kind: FznIdent, ident: vn))
        # Build: coeffs[0]*vars[0] + coeffs[1]*vars[1] + ... - rhs
        var linExpr1 = newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: -pair.rhs1),
            linear = true)
        for i in 0..<pair.coeffs1.len:
            linExpr1 = linExpr1 + pair.coeffs1[i] * exprs1[i]
        var linExpr2 = newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: -pair.rhs2),
            linear = true)
        for i in 0..<pair.coeffs2.len:
            linExpr2 = linExpr2 + pair.coeffs2[i] * exprs2[i]
        let zero = newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: 0),
            linear = true)
        let viol1 = binaryMax(zero, linExpr1)
        let viol2 = binaryMax(zero, linExpr2)
        let disjPenalty = binaryMin(viol1, viol2)
        result.sys.addConstraint(disjPenalty == 0)

        # Populate domain reduction metadata (positions instead of var names)
        block:
            var positions1: seq[int]
            var skip = false
            for vn in pair.varNames1:
                if vn in result.varPositions:
                    positions1.add(result.varPositions[vn])
                else:
                    skip = true
                    break
            if not skip:
                var positions2: seq[int]
                for vn in pair.varNames2:
                    if vn in result.varPositions:
                        positions2.add(result.varPositions[vn])
                    else:
                        skip = true
                        break
                if not skip:
                    result.sys.baseArray.disjunctivePairs.add((
                        coeffs1: pair.coeffs1, positions1: positions1, rhs1: pair.rhs1,
                        coeffs2: pair.coeffs2, positions2: positions2, rhs2: pair.rhs2))

    if result.sys.baseArray.disjunctivePairs.len > 0:
        stderr.writeLine(&"[FZN] Disjunctive pairs for domain reduction: {result.sys.baseArray.disjunctivePairs.len}")

    # Add generalized disjunctive clause constraints using dedicated DisjunctiveClauseType
    for clause in result.disjunctiveClauses:
        var disjuncts: seq[seq[tuple[coeffs: seq[int], positions: seq[int], rhs: int]]]
        var allPositions = initPackedSet[int]()
        var skip = false
        for disjunct in clause.disjuncts:
            var terms: seq[tuple[coeffs: seq[int], positions: seq[int], rhs: int]]
            for term in disjunct:
                var termPositions: seq[int]
                for vn in term.varNames:
                    if vn in result.varPositions:
                        termPositions.add(result.varPositions[vn])
                    elif vn in result.definedVarExprs:
                        # Defined var — can't use dedicated type, fall back
                        skip = true
                        break
                    else:
                        skip = true
                        break
                if skip: break
                terms.add((coeffs: term.coeffs, positions: termPositions, rhs: term.rhs))
                for p in termPositions:
                    allPositions.incl(p)
            if skip: break
            disjuncts.add(terms)

        if skip:
            # Fallback to algebraic expression for this clause
            let zero = newAlgebraicExpression[int](
                positions = initPackedSet[int](),
                node = ExpressionNode[int](kind: LiteralNode, value: 0),
                linear = true)
            var disjunctExprs: seq[AlgebraicExpression[int]]
            for disjunct in clause.disjuncts:
                var conjPenalty = zero
                for term in disjunct:
                    var linExpr = newAlgebraicExpression[int](
                        positions = initPackedSet[int](),
                        node = ExpressionNode[int](kind: LiteralNode, value: -term.rhs),
                        linear = true)
                    for i in 0..<term.coeffs.len:
                        let varExpr = result.resolveExprArg(FznExpr(kind: FznIdent, ident: term.varNames[i]))
                        linExpr = linExpr + term.coeffs[i] * varExpr
                    conjPenalty = conjPenalty + binaryMax(zero, linExpr)
                disjunctExprs.add(conjPenalty)
            var disjPenalty = disjunctExprs[0]
            for i in 1..<disjunctExprs.len:
                disjPenalty = binaryMin(disjPenalty, disjunctExprs[i])
            result.sys.addConstraint(disjPenalty == 0)
        else:
            # Emit dedicated DisjunctiveClauseConstraint
            let dcState = newDisjunctiveClauseConstraint[int](disjuncts)
            let constraint = StatefulConstraint[int](
                positions: allPositions,
                stateType: DisjunctiveClauseType,
                disjunctiveClauseState: dcState)
            result.sys.addConstraint(constraint)

    if result.disjunctiveClauses.len > 0:
        stderr.writeLine(&"[FZN] Emitted {result.disjunctiveClauses.len} generalized disjunctive clause constraints")

    # Emit value-support constraints
    for def in result.valueSupportDefs:
        let cellPos = result.varPositions[def.cellVarName]
        var neighbourPos: seq[int]
        for vn in def.neighbourVarNames:
            neighbourPos.add(result.varPositions[vn])
        result.sys.addConstraint(valueSupport[int](cellPos, neighbourPos, def.maxVal))
    if result.valueSupportDefs.len > 0:
        stderr.writeLine(&"[FZN] Emitted {result.valueSupportDefs.len} value-support constraints")

    # Emit synthetic relaxation constraints from product decomposition (for bounds propagation)
    for synTerm in result.syntheticRelaxations:
        var linExpr = newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: 0),
            linear = true)
        for i in 0..<synTerm.coeffs.len:
            let varExpr = result.resolveExprArg(FznExpr(kind: FznIdent, ident: synTerm.varNames[i]))
            linExpr = linExpr + synTerm.coeffs[i] * varExpr
        result.sys.addConstraint(linExpr <= synTerm.rhs)
    if result.syntheticRelaxations.len > 0:
        stderr.writeLine(&"[FZN] Added {result.syntheticRelaxations.len} synthetic relaxation " &
                          &"constraints for bounds propagation")

    # Emit cumulative constraints for detected disjunctive resource groups
    for group in result.disjunctiveResourceGroups:
        var positions: seq[int]
        var allResolved = true
        for vn in group.varNames:
            if vn in result.varPositions:
                positions.add(result.varPositions[vn])
            elif vn in result.definedVarExprs:
                # Defined var — shouldn't happen for start_time variables, but skip gracefully
                allResolved = false
                break
            else:
                allResolved = false
                break
        if not allResolved:
            continue
        let heights = newSeqWith(group.durations.len, 1)
        result.sys.addConstraint(cumulative[int](positions, group.durations, heights, 1))

    # Build NoOverlap constraints from detected patterns
    for pattern in result.noOverlapPatterns:
        var nodeA: array[3, FixedBoxEndpoint]
        var nodeB: array[3, FixedBoxEndpoint]
        var allResolved = true

        for d in 0..2:
            # Resolve endpoint A
            if pattern.nodeA[d].isFixed:
                nodeA[d] = FixedBoxEndpoint(isFixed: true, fixedValue: pattern.nodeA[d].fixedValue)
            else:
                if pattern.nodeA[d].varName notin result.varPositions:
                    allResolved = false
                    break
                nodeA[d] = FixedBoxEndpoint(isFixed: false, position: result.varPositions[pattern.nodeA[d].varName])

            # Resolve endpoint B
            if pattern.nodeB[d].isFixed:
                nodeB[d] = FixedBoxEndpoint(isFixed: true, fixedValue: pattern.nodeB[d].fixedValue)
            else:
                if pattern.nodeB[d].varName notin result.varPositions:
                    allResolved = false
                    break
                nodeB[d] = FixedBoxEndpoint(isFixed: false, position: result.varPositions[pattern.nodeB[d].varName])

        if not allResolved: continue

        result.sys.addConstraint(noOverlapFixedBox[int](
            nodeA, nodeB, pattern.radius, pattern.boxLower, pattern.boxUpper))

    if result.noOverlapPatterns.len > 0:
        stderr.writeLine(&"[FZN] Built {result.noOverlapPatterns.len} NoOverlapFixedBox constraints")

    # Build ConditionalNoOverlapPair constraints from detected patterns
    var nBuiltNoOverlap = 0
    template resolvePosName(name: string): int =
        if name == "": -1
        elif name in result.varPositions: result.varPositions[name]
        else: -1

    for info in result.conditionalNoOverlapInfos:
        let startAPos = resolvePosName(info.startAName)
        let startBPos = resolvePosName(info.startBName)
        if startAPos < 0: continue  # can't resolve

        let resourceAPos = resolvePosName(info.resourceAName)
        let resourceBPos = resolvePosName(info.resourceBName)
        let condAPos = resolvePosName(info.condAName)
        let condBPos = resolvePosName(info.condBName)

        if startAPos < 0 or startBPos < 0: continue

        result.sys.addConstraint(conditionalNoOverlapPair[int](
            startAPos, startBPos,
            info.durationA, info.durationB,
            resourceAPos, resourceBPos,
            info.resourceAFixed, info.resourceBFixed,
            condAPos, condBPos))
        nBuiltNoOverlap += 1

    if nBuiltNoOverlap > 0:
        stderr.writeLine(&"[FZN] Built {nBuiltNoOverlap} ConditionalNoOverlapPair constraints")

    # Build MultiResourceNoOverlap constraints from detected patterns
    var nBuiltMultiRes = 0
    for info in result.multiResourceNoOverlapInfos:
        let overlapPos = if info.overlapVarName in result.varPositions:
            result.varPositions[info.overlapVarName] else: -1
        if overlapPos < 0: continue

        var pairs: seq[AssignPair]
        var allResolved = true
        for (aName, bName) in info.assignPairNames:
            let aPos = if aName in result.varPositions: result.varPositions[aName] else: -1
            let bPos = if bName in result.varPositions: result.varPositions[bName] else: -1
            if aPos < 0 or bPos < 0:
                allResolved = false
                break
            pairs.add(AssignPair(posA: aPos, posB: bPos))
        if not allResolved: continue

        result.sys.addConstraint(multiResourceNoOverlap[int](overlapPos, pairs))
        nBuiltMultiRes += 1

    if nBuiltMultiRes > 0:
        stderr.writeLine(&"[FZN] Built {nBuiltMultiRes} MultiResourceNoOverlap constraints")

    # Build ConditionalCumulative constraints from detected patterns
    for ccinfo in result.conditionalCumulativeInfos:
        var fixedTasks: seq[FixedTask]
        for ft in ccinfo.fixedTasks:
            fixedTasks.add(FixedTask(start: ft.start, duration: ft.duration, height: ft.height))

        var condTasks: seq[ConditionalTask]
        var allResolved = true
        var maxTime = 0

        for ct in ccinfo.conditionalTasks:
            let roomPos = if ct.roomVarName in result.varPositions:
                result.varPositions[ct.roomVarName] else: -1
            if roomPos < 0:
                allResolved = false
                break

            var conditions: seq[TaskCondition]
            conditions.add(TaskCondition(position: roomPos, value: ct.roomValue))

            # Add selection condition if present
            if ct.selectionVarName != "":
                let selPos = if ct.selectionVarName in result.varPositions:
                    result.varPositions[ct.selectionVarName] else: -1
                if selPos < 0:
                    allResolved = false
                    break
                conditions.add(TaskCondition(position: selPos, value: 1))

            if ct.fixedAdmission >= 0 and ct.admissionVarName == "":
                # Fixed-admission task: conditional on room, but start time is constant
                condTasks.add(ConditionalTask(
                    startPosition: -1,
                    fixedStart: ct.fixedAdmission,
                    duration: ct.duration,
                    height: ct.height,
                    conditions: conditions
                ))
                maxTime = max(maxTime, ct.fixedAdmission + ct.duration)
            else:
                let admPos = if ct.admissionVarName in result.varPositions:
                    result.varPositions[ct.admissionVarName] else: -1
                if admPos < 0:
                    allResolved = false
                    break

                condTasks.add(ConditionalTask(
                    startPosition: admPos,
                    fixedStart: -1,
                    duration: ct.duration,
                    height: ct.height,
                    conditions: conditions
                ))

                # Estimate maxTime from admission domain upper bounds + duration
                let dom = result.sys.baseArray.domain[admPos]
                if dom.len > 0:
                    let maxAdm = dom[dom.len - 1]
                    maxTime = max(maxTime, maxAdm + ct.duration)

        if not allResolved: continue

        # Also account for fixed tasks in maxTime
        for ft in fixedTasks:
            maxTime = max(maxTime, ft.start + ft.duration)

        result.sys.addConstraint(conditionalCumulative[int](fixedTasks, condTasks, ccinfo.limit, maxTime))

    if result.conditionalCumulativeInfos.len > 0:
        stderr.writeLine(&"[FZN] Built {result.conditionalCumulativeInfos.len} ConditionalCumulative constraints")

    # Build ConditionalDayCapacity constraints
    for cdcinfo in result.conditionalDayCapacityInfos:
        var tasks: seq[DayCapacityTask]
        var allResolved = true
        for tinfo in cdcinfo.tasks:
            let admPos = result.varPositions.getOrDefault(tinfo.admissionVarName, -1)
            var selPos = -1
            if tinfo.selectionVarName != "" and not tinfo.isMandatory:
                selPos = result.varPositions.getOrDefault(tinfo.selectionVarName, -1)
            if admPos < 0 or (selPos < 0 and tinfo.selectionVarName != "" and not tinfo.isMandatory):
                stderr.writeLine(&"[FZN] WARNING: ConditionalDayCapacity task variable not found: adm={tinfo.admissionVarName}({admPos}) sel={tinfo.selectionVarName}({selPos})")
                allResolved = false
                break
            var extraPos = -1
            if tinfo.extraCondVarName != "":
                extraPos = result.varPositions.getOrDefault(tinfo.extraCondVarName, -1)
                if extraPos < 0:
                    stderr.writeLine(&"[FZN] WARNING: ConditionalDayCapacity extra condition variable not found: {tinfo.extraCondVarName}")
                    allResolved = false
                    break
            tasks.add(DayCapacityTask(
                weight: tinfo.weight,
                admissionPos: admPos,
                selectionPos: selPos,
                selectionVal: 1,  # selection[p] == true (1)
                extraCondPos: extraPos,
                extraCondVal: tinfo.extraCondVal))
        if not allResolved: continue
        result.sys.addConstraint(conditionalDayCapacity[int](tasks, cdcinfo.capacities, cdcinfo.maxDay))

    if result.conditionalDayCapacityInfos.len > 0:
        stderr.writeLine(&"[FZN] Built {result.conditionalDayCapacityInfos.len} ConditionalDayCapacity constraints")

    # Detect transition table chains and apply bidirectional multi-hop reachability
    # domain reduction. MiniZinc may eliminate boundary variables (e.g., agentAtTimeT[1,a]=58
    # becomes a constant). We extract the graph from transition tables, identify the chain
    # structure from the output array, and compute forward/backward BFS to restrict all
    # timestep variables — not just the ones adjacent to boundaries.
    block:
        # Build adjacency from tables: condPos → targetPos → tuples
        var tableGraph: Table[int, Table[int, seq[seq[int]]]]
        for cons in result.sys.baseArray.constraints:
            if cons.stateType != TableConstraintType: continue
            let tbl = cons.tableConstraintState
            if tbl.mode != TableIn or tbl.sortedPositions.len != 2: continue
            if tbl.tuples.len < MinTransitionTableSize: continue  # Skip small (non-transition) tables
            let p0 = tbl.sortedPositions[0]
            let p1 = tbl.sortedPositions[1]
            if p0 notin tableGraph:
                tableGraph[p0] = initTable[int, seq[seq[int]]]()
            tableGraph[p0][p1] = tbl.tuples

        if tableGraph.len > 0:
            # Extract graph adjacency as union across ALL transition tables
            var graphAdj: Table[int, PackedSet[int]]  # node -> forward neighbors
            var reverseAdj: Table[int, PackedSet[int]]  # node -> backward neighbors
            for condPos, targets in tableGraph:
                for targetPos, tuples in targets:
                    for t in tuples:
                        if t[0] notin graphAdj:
                            graphAdj[t[0]] = initPackedSet[int]()
                        graphAdj[t[0]].incl(t[1])
                        if t[1] notin reverseAdj:
                            reverseAdj[t[1]] = initPackedSet[int]()
                        reverseAdj[t[1]].incl(t[0])

            if graphAdj.len > 0:
                # Find chain structure from output arrays
                for arrName, arrPositions in result.arrayPositions:
                    if arrPositions.len < 20: continue
                    # Skip arrays with eliminated variables (position=-1 sentinel from defined var elimination)
                    var hasEliminatedVars = false
                    for pos in arrPositions:
                        if pos < 0:
                            hasEliminatedVars = true
                            break
                    if hasEliminatedVars: continue
                    # Detect stride from initial singletons (eliminated boundary variables)
                    var startSingletons = 0
                    for i in 0..<arrPositions.len:
                        if result.sys.baseArray.domain[arrPositions[i]].len == 1:
                            inc startSingletons
                        else:
                            break
                    if startSingletons == 0: continue
                    let stride = startSingletons

                    # Verify first row of variables exists
                    if arrPositions.len <= stride: continue
                    if result.sys.baseArray.domain[arrPositions[stride]].len <= 1: continue

                    # Detect end singletons
                    var endSingletons = 0
                    for i in countdown(arrPositions.len - 1, 0):
                        if result.sys.baseArray.domain[arrPositions[i]].len == 1:
                            inc endSingletons
                        else:
                            break

                    # Compute number of timesteps: total array / stride
                    let totalSteps = arrPositions.len div stride
                    if totalSteps < 3: continue
                    if stride * totalSteps != arrPositions.len: continue

                    # Validate this is actually a transition chain: check that consecutive
                    # timestep positions for ALL agents have table constraints between them.
                    # This prevents false matches on non-transition arrays that happen to have
                    # leading singletons and pass the length divisibility check.
                    var isChain = true
                    for a in 0..<stride:
                        for t in 0..<totalSteps - 1:
                            let p0 = arrPositions[t * stride + a]
                            let p1 = arrPositions[(t + 1) * stride + a]
                            if p0 notin tableGraph or p1 notin tableGraph[p0]:
                                isChain = false
                                break
                        if not isChain: break
                    if not isChain: continue

                    # Extract start and end values per agent
                    var startValues: seq[int]
                    var endValues: seq[int]
                    var hasStart = true
                    var hasEnd = (endSingletons == stride)
                    for a in 0..<stride:
                        let sPos = arrPositions[a]
                        if result.sys.baseArray.domain[sPos].len != 1:
                            hasStart = false
                            break
                        startValues.add(result.sys.baseArray.domain[sPos][0])
                    if not hasStart: continue

                    if hasEnd:
                        for a in 0..<stride:
                            let ePos = arrPositions[(totalSteps - 1) * stride + a]
                            if result.sys.baseArray.domain[ePos].len != 1:
                                hasEnd = false
                                break
                            endValues.add(result.sys.baseArray.domain[ePos][0])

                    # Bidirectional BFS: compute reachable sets per agent per timestep
                    var nChainRestrictions = 0
                    for a in 0..<stride:
                        # Forward BFS from start node
                        var forward: seq[PackedSet[int]]
                        forward.setLen(totalSteps)
                        forward[0].incl(startValues[a])
                        for t in 1..<totalSteps:
                            for node in forward[t-1].items:
                                if node in graphAdj:
                                    forward[t] = forward[t] + graphAdj[node]

                        # Backward BFS from end node (if known)
                        var backward: seq[PackedSet[int]]
                        if hasEnd:
                            backward.setLen(totalSteps)
                            backward[totalSteps - 1].incl(endValues[a])
                            for t in countdown(totalSteps - 2, 0):
                                for node in backward[t+1].items:
                                    if node in reverseAdj:
                                        backward[t] = backward[t] + reverseAdj[node]

                        # Restrict domains at each non-boundary timestep
                        for t in 1..<totalSteps - (if hasEnd: 1 else: 0):
                            let pos = arrPositions[t * stride + a]
                            let currentDom = result.sys.baseArray.domain[pos]
                            if currentDom.len <= 1: continue

                            # Intersect with forward reachability
                            var reachable = forward[t]
                            # Intersect with backward reachability if available
                            if hasEnd and backward[t].len > 0:
                                reachable = reachable * backward[t]

                            if reachable.len == 0: continue  # Safety: don't empty a domain

                            var newDom: seq[int]
                            for v in currentDom:
                                if v in reachable:
                                    newDom.add(v)
                            if newDom.len > 0 and newDom.len < currentDom.len:
                                result.sys.baseArray.setDomain(pos, newDom)
                                inc nChainRestrictions

                    if nChainRestrictions > 0:
                        stderr.writeLine(&"[FZN] Bidirectional reachability restrictions: {nChainRestrictions} positions ({stride} agents, {totalSteps} timesteps)")

    # Add geost constraint if conversion is active
    if result.geostConversion.tileValues.len > 0:
        result.sys.addConstraint(geost[int](
            result.geostConversion.tileVarPositions,
            result.geostConversion.allPlacements
        ))

    # Detect constant-element sources for downstream composition (eliminates cascade hops)
    # MUST run before detectSharedIndexConsolidation (which removes some element constraints from channelConstraints)
    result.detectConstantElementComposition()

    # Consolidate shared-index element channels into table constraints
    # MUST run after translateVariables (positions exist) and before buildChannelBindings
    result.detectSharedIndexConsolidation()

    # Record binding count from constraint loop (table_int functional deps, array_set_element, etc.)
    let constraintLoopBindingCount = result.sys.baseArray.channelBindings.len

    # Build channel bindings for element defines_var
    result.buildChannelBindings()
    # Build channel bindings for synthetic element channels (conditional gain variables)
    result.buildSyntheticElementChannelBindings()
    # Build channel bindings for int_mod channels (Z = X mod C → element lookup)
    result.buildIntModChannelBindings()
    # Build channel bindings for singleton set booleans (S.bools = indicator(x))
    result.buildSingletonSetChannelBindings()
    # Build channel bindings for int_eq_reif/bool2int reification channels
    result.buildReifChannelBindings()
    # Build channel bindings for bool AND channels (b = AND(c1,...,cn) from bool_clause)
    result.buildBoolAndChannelBindings()
    # Build channel bindings for conditional implication channels (binary + one-hot)
    result.buildConditionalImplicationChannelBindings()
    # Build channel bindings for bool equivalence aliases (identity element channels)
    result.buildBoolEquivAliasBindings()
    # Build channel bindings for bool-gated variable channels (x = if cond then y else const)
    result.buildBoolGatedVarChannelBindings()
    # Build channel bindings for array_bool_and/or with defines_var
    result.buildBoolLogicChannelBindings()
    # Build channel bindings for one-hot indicator variables
    result.buildOneHotChannelBindings()
    # Detect implicit min/max channels: array_int_max/min without defines_var
    # that are only used as outputs (not referenced as inputs elsewhere).
    # Must run before buildMinMaxChannelBindings so new entries are processed.
    result.detectImplicitMaxChannels()
    # Build channel bindings for array_int_minimum/maximum defines_var
    result.buildMinMaxChannelBindings()
    # Build channel bindings for rescued defined vars (from var-indexed arrays)
    result.buildRescuedChannelBindings()
    # Build channel bindings for set_union defines_var (max of boolean pairs)
    result.buildSetUnionChannelBindings()
    # Build channel bindings for case-analysis channels (constant lookup tables)
    result.buildCaseAnalysisChannelBindings()
    # Build inverse channel groups (inverse relationship: seat[person[p]] = p)
    result.buildInverseChannelBindings()
    # Detect dormant positions in diffnK constraints (don't-care placements)
    result.detectDormantPositions()

    # Deduplicate element channel bindings.
    # Phase A: remove builder-phase bindings that conflict with constraint-loop bindings
    #          (e.g., table_int creates a functional dep channel, then buildReifChannelBindings
    #          creates a bool2int for the same position).
    # Phase B: remove constraint-loop-vs-constraint-loop duplicates (e.g., two fzn_table_int
    #          constraints that both claim the same position as a functional dependency).
    #          The second binding is demoted to a regular element constraint.
    block:
        # Phase A: collect positions claimed by constraint-loop bindings
        var constraintLoopPositions: PackedSet[int]
        for i in 0..<constraintLoopBindingCount:
            constraintLoopPositions.incl(result.sys.baseArray.channelBindings[i].channelPosition)

        var dedupCount = 0
        var kept: seq[ChannelBinding[int]]

        # Phase B: also track within-constraint-loop duplicates
        var seenConstraintLoopPositions: PackedSet[int]

        for i, binding in result.sys.baseArray.channelBindings:
            if i >= constraintLoopBindingCount and binding.channelPosition in constraintLoopPositions:
                # Builder binding conflicts with constraint-loop binding — skip
                inc dedupCount
            elif i < constraintLoopBindingCount and binding.channelPosition in seenConstraintLoopPositions:
                # Constraint-loop duplicate: demote to element constraint.
                # Use elementExpr (supports complex index exprs like BinaryOpNode from composite keys).
                let channelPosExpr = result.sys.baseArray[binding.channelPosition]
                var allConst = true
                for elem in binding.arrayElements:
                    if not elem.isConstant: allConst = false; break
                if allConst:
                    var constArr: seq[int]
                    for elem in binding.arrayElements: constArr.add(elem.constantValue)
                    result.sys.addConstraint(elementExpr[int](binding.indexExpression, constArr, channelPosExpr))
                else:
                    var arrayExprs: seq[AlgebraicExpression[int]]
                    for elem in binding.arrayElements:
                        if elem.isConstant:
                            arrayExprs.add(newAlgebraicExpression[int](
                                positions = initPackedSet[int](),
                                node = ExpressionNode[int](kind: LiteralNode, value: elem.constantValue),
                                linear = true))
                        else:
                            arrayExprs.add(result.sys.baseArray[elem.variablePosition])
                    result.sys.addConstraint(elementExpr[int](binding.indexExpression, arrayExprs, channelPosExpr))
                inc dedupCount
            else:
                if i < constraintLoopBindingCount:
                    seenConstraintLoopPositions.incl(binding.channelPosition)
                kept.add(binding)
        if dedupCount > 0:
            result.sys.baseArray.channelBindings = kept
            # Rebuild channelsAtPosition from scratch
            result.sys.baseArray.channelsAtPosition.clear()
            for bi, binding in result.sys.baseArray.channelBindings:
                for pos in binding.indexExpression.positions.items:
                    if pos notin result.sys.baseArray.channelsAtPosition:
                        result.sys.baseArray.channelsAtPosition[pos] = @[bi]
                    else:
                        result.sys.baseArray.channelsAtPosition[pos].add(bi)
                for elem in binding.arrayElements:
                    if not elem.isConstant:
                        let pos = elem.variablePosition
                        if pos notin result.sys.baseArray.channelsAtPosition:
                            result.sys.baseArray.channelsAtPosition[pos] = @[bi]
                        elif bi notin result.sys.baseArray.channelsAtPosition[pos]:
                            result.sys.baseArray.channelsAtPosition[pos].add(bi)
            stderr.writeLine(&"[FZN] Deduplicated {dedupCount} element channel bindings ({kept.len} remaining)")

    result.translateSolve()

    # Tighten objective lower bound: if objective is max(diff_i) where each diff_i = max(counts) - min(counts),
    # then objective >= 0 since max >= min for the same input set.
    if result.model.solve.kind == Minimize and result.objectivePos >= 0:
        let carray = result.sys.baseArray
        # Build position-to-minmax-binding map
        var posToBind: Table[int, int]  # position → binding index
        for i, b in carray.minMaxChannelBindings:
            posToBind[b.channelPosition] = i
        # Check if objective position is a max channel
        if result.objectivePos in posToBind:
            let objBind = carray.minMaxChannelBindings[posToBind[result.objectivePos]]
            if not objBind.isMin:
                # Build paired max/min sets: positions where (maxPos, minPos) share the same inputs.
                # Uses a hash map from sorted input position seqs to channel positions for O(n) pairing.
                var pairedNonNeg: PackedSet[int]  # positions where max-min >= 0
                var minByInputs: Table[seq[int], int]  # sorted input positions → min channel position
                for i, b in carray.minMaxChannelBindings:
                    var inputPos: seq[int]
                    for e in b.inputExprs:
                        for p in e.positions.items: inputPos.add(p)
                    inputPos.sort()
                    if b.isMin:
                        minByInputs[inputPos] = b.channelPosition
                    else:
                        if inputPos in minByInputs:
                            # max and min on same inputs: max - min >= 0
                            pairedNonNeg.incl(b.channelPosition)
                            pairedNonNeg.incl(minByInputs[inputPos])
                # Check if all objective inputs reference only paired positions
                if pairedNonNeg.len > 0:
                    var allNonNeg = true
                    for inputExpr in objBind.inputExprs:
                        for p in inputExpr.positions.items:
                            if p notin pairedNonNeg:
                                allNonNeg = false; break
                        if not allNonNeg: break
                    if allNonNeg:
                        let oldLo = result.objectiveLoBound
                        result.objectiveLoBound = max(result.objectiveLoBound, 0)
                        if result.objectiveLoBound != oldLo:
                            stderr.writeLine(&"[FZN] Objective lower bound tightened: {oldLo} → {result.objectiveLoBound}")

    # Detect partition groups: sum-of-channels == 1 constraints where channels
    # trace back through bool2int → int_ne_reif to search positions.
    # These enable partition-aware swap moves in the tabu search.
    block:
        let carray = result.sys.baseArray
        # Build reverse map: channel position → channel binding index
        var chanPosToBind = initTable[int, int]()
        for bi, binding in carray.channelBindings:
            chanPosToBind[binding.channelPosition] = bi

        # Extract null value from a ne_reif lookup array.
        # For int_ne_reif(x, val, b): array is [0 if v==val else 1 for v in lo..hi].
        # Returns (nullVal, true) on success, (0, false) on failure.
        proc extractNullValue(binding: ChannelBinding[int], domain: seq[int]): (int, bool) =
            if domain.len == 0: return (0, false)
            let lo = domain[0]
            for idx, elem in binding.arrayElements:
                if elem.isConstant and elem.constantValue == 0:
                    return (lo + idx, true)
            return (0, false)

        var nGroups = 0
        var totalMembers = 0

        for constraint in carray.constraints:
            if constraint.stateType != RelationalType: continue
            let rc = constraint.relationalState
            if rc.relation != EqualTo: continue

            # Check for sum(channels) == 1 pattern
            # Left side should be a PositionBased SumExpr, right side constant 1
            var sumExpr: SumExpression[int] = nil
            var rhsVal: int = 0
            if rc.leftExpr.kind == SumExpr and rc.rightExpr.kind == ConstantExpr:
                sumExpr = rc.leftExpr.sumExpr
                rhsVal = rc.rightExpr.constantValue
            elif rc.rightExpr.kind == SumExpr and rc.leftExpr.kind == ConstantExpr:
                sumExpr = rc.rightExpr.sumExpr
                rhsVal = rc.leftExpr.constantValue
            else:
                continue

            if rhsVal != 1: continue
            if sumExpr.evalMethod != PositionBased: continue

            # Check all coefficients are 1 and all positions are channels
            var allOnes = true
            var allChannels = true
            var sumPositions: seq[int] = @[]
            for pos, coeff in sumExpr.coefficient:
                sumPositions.add(pos)
                if coeff != 1:
                    allOnes = false
                    break
                if pos notin carray.channelPositions:
                    allChannels = false
                    break
            if not allOnes or not allChannels: continue
            if sumPositions.len < 2: continue

            # Trace each channel position back to search positions
            var searchPositions: seq[int] = @[]
            var nullValue = 0
            var valid = true
            var nullValueSet = false

            for chanPos in sumPositions:
                if chanPos notin chanPosToBind:
                    valid = false
                    break
                let bi1 = chanPosToBind[chanPos]
                let bind1 = carray.channelBindings[bi1]

                # This should be bool2int: element(boolPos, [0, 1])
                # The indexExpression should reference one source position
                var sourcePos1 = -1
                for p in bind1.indexExpression.positions.items:
                    if sourcePos1 >= 0:
                        sourcePos1 = -1  # More than one position — not simple
                        break
                    sourcePos1 = p

                if sourcePos1 < 0:
                    valid = false
                    break

                # Check if source is itself a channel (ne_reif layer)
                if sourcePos1 in carray.channelPositions:
                    if sourcePos1 notin chanPosToBind:
                        valid = false
                        break
                    let bi2 = chanPosToBind[sourcePos1]
                    let bind2 = carray.channelBindings[bi2]

                    # Extract search position from ne_reif binding
                    var sourcePos2 = -1
                    for p in bind2.indexExpression.positions.items:
                        if sourcePos2 >= 0:
                            sourcePos2 = -1
                            break
                        sourcePos2 = p

                    if sourcePos2 < 0 or sourcePos2 in carray.channelPositions:
                        valid = false
                        break

                    let (thisNullVal, foundNull) = extractNullValue(bind2, carray.domain[sourcePos2])
                    if not foundNull:
                        valid = false
                        break
                    if nullValueSet:
                        if thisNullVal != nullValue:
                            valid = false
                            break
                    else:
                        nullValue = thisNullVal
                        nullValueSet = true

                    searchPositions.add(sourcePos2)
                else:
                    # Source is already a search position (single layer)
                    let (thisNullVal, foundNull) = extractNullValue(bind1, carray.domain[sourcePos1])
                    if not foundNull:
                        valid = false
                        break
                    if nullValueSet:
                        if thisNullVal != nullValue:
                            valid = false
                            break
                    else:
                        nullValue = thisNullVal
                        nullValueSet = true

                    searchPositions.add(sourcePos1)

            if not valid or searchPositions.len < 2 or not nullValueSet:
                continue

            result.sys.baseArray.partitionGroups.add(
                PartitionGroup[int](searchPositions: searchPositions, nullValue: nullValue))
            inc nGroups
            totalMembers += searchPositions.len

        if nGroups > 0:
            stderr.writeLine(&"[FZN] Detected {nGroups} partition groups ({totalMembers} total members)")

    # Build WeightedSameValueExpression if pattern was detected
    if result.weightedSameValueObjName != "":
        var wsvPairs: seq[WeightedSameValuePair[int]]
        for pair in result.weightedSameValuePairs:
            let posA = result.varPositions[pair.varNameA]
            let posB = result.varPositions[pair.varNameB]
            wsvPairs.add((posA: posA, posB: posB, coeff: pair.coeff))
        result.weightedSameValueExpr = newWeightedSameValueExpression[int](
            wsvPairs, result.weightedSameValueConstant)
