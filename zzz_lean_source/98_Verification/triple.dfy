method Triple (x: int) returns (r : int)
ensures r == 3*x;
{
    return x + x + x;
}