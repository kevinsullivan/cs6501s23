# A function to c the square root of
# a number, n, to within a tolerance
# of e, using Newtons method
def squareRoot(n, e):
    x = n
    while (True):
        root = 0.5 * (x + (n / x))
        if (abs(root - x) < e):
            break
        x = root
    return root


# Driver code
if __name__ == "__main__":
    n = 900
    sqrt_900 = squareRoot(n, 0.00001)
    print("The approximate square root of ", n, " is ", sqrt_900)
    print("The error is approximately ", abs(sqrt_900**2 - 900))
