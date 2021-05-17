module Utils
{
    method integerToCharSequence(val : int) returns (result : seq<char>)
    {
        if (val == 0) {
            return "0";
        }

        var digits : seq<char> := "0123456789";
        var nr := val;
        result := "";

        if (nr < 0) {
            nr := -nr;
        }

        assert nr >= 0;

        while (nr > 0)
            decreases nr;
        {
            var a := nr % 10;
            nr := nr / 10;
            result := [digits[a]] + result;
        }
        
        if (val < 0) {
            result := "-" + result;
        }
    }

    function pow(exp : int, power : int) : (res : int)
        requires power >= 0;
        requires exp > 0;
        ensures res > 0;
        decreases power;
    {
        if (power == 0) then
            1
        else
            exp * pow(exp, power - 1)
    }

    lemma pow_monotone(a : int, b : int)
        requires 0 <= a <= b;
        ensures pow(2, a) <= pow(2, b);
    {
    }

    lemma pow_monotone_strict(a : int, b : int)
        requires 0 <= a < b;
        ensures pow(2, a) < pow(2, b);
    {
    }

    lemma multpow_powsum(a : int, b : int)
        requires a >= 1;
        requires b >= 1;
        ensures pow(2, a) * pow(2, b) == pow(2, a + b);
    {
        if(b > 2) {
            multpow_powsum(a, b - 1);
        }
        assert pow(2, a) * pow(2, 2) == pow(2, a + 2);
    }

    lemma sumpow_upper(a : int, b : int)
        requires a >= 1;
        requires b >= 2; // needs to be at least 2
        requires a >= b;
        ensures pow(2, a) + pow(2, b) + 1 < pow(2, a * b);
    {
        pow_monotone(a * 2, a * b);
        assert pow(2, a * 2) <= pow(2, a * b);
        assert pow(2, a + a) <= pow(2, a * 2);
        multpow_powsum(a, a);
        assert pow(2, a) * pow(2, a) <= pow(2, a + a);
        
        assert 4 <= pow(2, a);
        assert 4 * pow(2, a) <= pow(2, a) * pow(2, a);
        assert pow(2, a) + pow(2, a) + pow(2, a) + pow(2, a) <= 4 * pow(2, a);
        pow_monotone(b, a);
        assert pow(2, b) <= pow(2, a);
        assert pow(2, a) + pow(2, b) + 1 <
            pow(2, a) + pow(2, a) + pow(2, a) + pow(2, a);
    }

    lemma mult2_upper(x : int)
        requires x >= 0;
        ensures 2 * x < 1 + pow(2, x);
    {
    }

    lemma lessthan_mult_right(a : int, b : int, c : int)
        requires a >= 1;
        requires b >= 1;
        requires c >= 1;
        requires c < b;
        ensures a * c < a * b;
    {
    }

    lemma pow_increases(a : int)
        requires a >= 1;
        ensures a < pow(2, a);
    {
    }

    function method max(val1 : int, val2 : int) : (result : int)
        ensures result == val1 || result == val2;
        ensures result >= val1;
        ensures result >= val2;
    {
        if (val1 >= val2) then
            val1
        else
            val2
    }

    predicate smaller(a : (int, int, int, int, int),
        b : (int, int, int, int, int))
    {
        a.0 < b.0 ||
            (a.0 <= b.0 && a.1 < b.1) || 
            (a.0 <= b.0 && a.1 <= b.1 && a.2 < b.2) || 
            (a.0 <= b.0 && a.1 <= b.1 && a.2 <= b.2 && a.3 < b.3) || 
            (a.0 <= b.0 && a.1 <= b.1 && a.2 <= b.2 && a.3 <= b.3 && a.4 < b.4)
    }

    function nFalses(n : int) : seq<bool>
        requires n >= 0;
        ensures |nFalses(n)| == n
    {
        if n == 0 then
            []
        else
            nFalses(n - 1) + [false]
    }
}
