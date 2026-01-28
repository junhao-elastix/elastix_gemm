package common_pkg;

    function automatic int cdiv(input int x, input int y);
        return (x + y - 1) / y;
    endfunction

    function automatic int max(input int x, input int y);
        return (x > y) ? x : y;
    endfunction

endpackage