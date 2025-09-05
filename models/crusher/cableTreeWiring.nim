import std/[os, sequtils, strformat, strutils, math]

import crusher

proc cableTreeWiring*(k: int, b: int) =
    # Cable Tree Wiring Problem
    # k = number of positions/cavities (80)
    # b = number of cable pairs (40)
    
    var sys = initConstraintSystem[int]()
    
    # Main decision variables: pfc[i] = position of cavity i
    var pfc = sys.newConstrainedSequence(k)
    pfc.setDomain(toSeq(1..k))
    
    # All positions must be different (permutation constraint)
    sys.addConstraint(allDifferent(pfc))
    
    # Atomic constraints: pfc[i] < pfc[j] for specific (i,j) pairs
    # These would be loaded from the AtomicConstraints array in A022.dzn
    # For now, adding a few examples:
    let atomicConstraints = [
        (14, 1), (14, 12), (14, 16), (15, 1), (15, 12), (15, 16),
        # ... would need all 380 pairs from the data file
    ]
    
    for (i, j) in atomicConstraints:
        if i <= k and j <= k:
            sys.addConstraint(pfc[i-1] < pfc[j-1])  # Convert to 0-based indexing
    
    # Direct successor constraints
    # if DirectSuccessors[i] <= b then 
    #   pfc[DirectSuccessors[i]] < pfc[DirectSuccessors[i]+b] -> pfc[DirectSuccessors[i]] +1 = pfc[DirectSuccessors[i]+b]
    for i in 1..b:
        let directSucc = i  # DirectSuccessors[i] = i for this problem
        if directSucc <= b:
            # This is a conditional constraint that would need custom implementation
            # For now, just enforce the ordering part
            sys.addConstraint(pfc[directSucc-1] < pfc[directSucc+b-1])
    
    # Disjunctive constraints would need custom constraint implementation
    # These are complex: (pfc[i] < pfc[j] OR pfc[k] < pfc[l]) AND additional conditions
    
    # Objective function components (would need to be computed after solving)
    # S = sum of violations of direct successor constraints  
    # M = maximum crossings
    # L = maximum cable length
    # N = violations of soft constraints
    
    echo fmt"Cable Tree Wiring problem with k={k}, b={b}"
    echo fmt"Variables: {pfc.len}"
    echo fmt"Solving..."
    
    sys.resolve()
    
    if sys.assignment.len > 0:
        echo "Solution found:"
        echo fmt"pfc = {pfc.assignment}"
        
        # Compute objective components
        var S = 0
        var violations: seq[int] = @[]
        for i in 1..b:
            let pos1 = sys.assignment[i-1]
            let pos2 = sys.assignment[i+b-1] 
            let diff = abs(pos1 - pos2)
            if diff > 1:
                S += 1
                violations.add(diff - 1)
        
        echo fmt"S (successor violations) = {S}"
        echo fmt"Objective contribution from S = {S * k * k * k}"
    else:
        echo "No solution found"

when isMainModule:
    if paramCount() >= 2:
        let k = parseInt(paramStr(1))
        let b = parseInt(paramStr(2))
        cableTreeWiring(k, b)
    else:
        echo "Usage: ./cableTreeWiring k b"
        echo "Example: ./cableTreeWiring 80 40"