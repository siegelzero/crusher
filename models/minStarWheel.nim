import std/[os, sequtils, strutils]

import crusher


proc star(n: int): seq[int] =
    let bound = n*(n + 1)

    var best = bound;
    var pn = 1
    var bits = newSeq[bool](bound + 1)

    for p in @[2, 3, 5, 7, 11, 13]:
        pn *= p
        if pn > best:
            break
        for pk in countup(p, bound, p):
            bits[pk] = true
        
        bits[pn] = false
        var count = 0
        var psum = 0
        var terms: seq[int]

        for i in 0..bound:
            if bits[i]:
                terms.add(i)
                count += 1
                psum += i
                if count == n - 1:
                    if pn + psum < best:
                        best = pn + psum
                        result = terms
                    break
        
        bits[pn] = true


proc minStarWheel*(n: int) =
    #var starEntries = @[2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28, 30, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 60, 62, 63, 64, 65, 66, 68, 69, 70, 72, 74, 75, 76, 77, 78, 80, 81, 82, 84, 85, 86, 87, 88, 90, 91, 92, 93, 94, 95, 96, 98, 99, 100, 102, 104, 105, 106, 108, 110, 111, 112, 114, 115, 116, 117, 118, 119, 120, 122, 123, 124, 125, 126, 128, 129, 130, 132, 133, 134, 135, 136, 138, 140, 141, 142, 144, 145, 146, 147, 148, 150, 152, 153, 154, 155, 156, 158, 159, 160, 161, 162, 164, 165, 166, 168, 170, 171, 172, 174, 175, 176, 177, 178, 180, 182, 183, 184, 185, 186, 188, 189, 190, 192, 194, 195, 196, 198, 200, 201, 202, 203, 204, 205, 206, 207, 208, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 224, 225, 226, 228, 230, 231, 232, 234, 235, 236, 237, 238, 240, 242, 243, 244, 245, 246, 248, 249, 250, 252, 254, 255, 256, 258, 259]
    var starEntries = star(n)
    var n = len(starEntries)

    var sys = initConstraintSystem[int]()
    var label = sys.newConstrainedSequence(n)
    label.setDomain(starEntries)

    sys.addConstraint(allDifferent(label))

    for i in 0..<n-1:
        sys.addConstraint(commonFactor(label[i], label[i + 1]))
    sys.addConstraint(commonFactor(label[n - 1], label[0]))

    sys.resolve()

    echo n + 1


when isMainModule:
    let a = parseInt(paramStr(1))
    let b = parseInt(paramStr(2))
    for k in a..b:
        minStarWheel(k)