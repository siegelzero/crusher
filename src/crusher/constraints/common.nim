################################################################################
# Common types and enums shared across multiple constraint modules
################################################################################

type
    StateEvalMethod* = enum
        ## Evaluation method for constraints that can work on either
        ## direct position values or computed expressions
        ExpressionBased,  # Constraint evaluates expressions (e.g., x[i] + i)
        PositionBased     # Constraint evaluates direct position values (e.g., x[i])