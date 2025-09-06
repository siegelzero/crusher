func gcd*(x, y: int): int =
    if x < y:
        return gcd(y, x)
    var xx, yy: int
    xx = x
    yy = y

    while yy > 0:
        (xx, yy) = (yy, xx mod yy)

    return xx
