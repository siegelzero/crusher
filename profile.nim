import std/[os, packedsets, strformat, strutils, times]

import state/[arrayState, domain]
import constraintSystem
import heuristics/tabuSearch
import models


when isMainModule:
   let n = parseInt(paramStr(1))
   let tenure = parseInt(paramStr(2))
   let threshold = parseInt(paramStr(3))
   #let x = MOLSSystem(n)
   #let x = latinSquareSystem(n)
   #let x = sendMoreMoney()
   #let x = ageProblem()
   # let x = magicSquare(n)
   let x = magicSquareLC(n)
   #let x = nQueens2(n)
   #let x = lcTest()
   # let x = langford(n)

   let then = epochTime()

   x.resolve(tenure, threshold)

   var pos = x.variables[0]

   var lseq = newSeq[int](2*n)
   var ass = pos.getAssignment()
   pos.display()

   # echo ass

   # for i in 0..<n:
   #    lseq[ass[i]] = i + 1
   #    lseq[ass[i + n]] = i + 1
   # echo lseq

   let now = epochTime()
   let diff = now - then
   echo fmt"Elapsed Time: {diff:.3f}"
