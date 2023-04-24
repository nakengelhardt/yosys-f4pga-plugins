localparam WABITS = 9;
localparam WDBITS = 18;

localparam RABITS = WABITS;
localparam RDBITS = WDBITS;

localparam DEPTH = 2**(WABITS+1);

localparam BYTEWIDTH = 9;
localparam NBYTES = WDBITS/BYTEWIDTH;