import std/[os, packedsets, strformat, strutils, times]

import state/[arrayState, domain]
import constraintSystem
import heuristics/tabuSearch
import models


when isMainModule:
    let n = parseInt(paramStr(1))
    let tenure = parseInt(paramStr(2))
    let threshold = parseInt(paramStr(3))
    # let x = MOLSSystem(n)
   #  let x = latinSquareSystem(n)
    # let x = sendMoreMoney()
    # let x = ageProblem()
   #  let x = magicSquare(n)
   #  let x = magicSquareLC(n)
    let x = nQueens2(n)
   #  let x = lcTest()
    
    let then = epochTime()

    echo x.findAssignment(tenure, threshold)

   #  for v in x.variables:
   #     display(v)
   #     echo ""

    let now = epochTime()
    let diff = now - then
    echo fmt"Elapsed Time: {diff:.3f}"
