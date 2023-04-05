localparam WABITS = 12;
localparam WDBITS = 18;

localparam RABITS = WABITS;
localparam RDBITS = WDBITS;

localparam DEPTH = 2**WABITS;

localparam BYTEWIDTH = 9;
localparam NBYTES = WDBITS/BYTEWIDTH;