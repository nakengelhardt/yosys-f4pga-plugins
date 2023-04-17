module \$__QLF_TDP36K (...);

parameter INIT = 0;

parameter PORT_A_WIDTH = 1;
parameter PORT_A_WR_BE_WIDTH = 1;

parameter PORT_B_WIDTH = 1;
parameter PORT_B_WR_BE_WIDTH = 1;

input PORT_A_CLK;
input [14:0] PORT_A_ADDR;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
input PORT_A_WR_EN;
input [PORT_A_WR_BE_WIDTH-1:0] PORT_A_WR_BE;
input PORT_A_CLK_EN;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;

input PORT_B_CLK;
input [14:0] PORT_B_ADDR;
input [PORT_B_WIDTH-1:0] PORT_B_WR_DATA;
input PORT_B_WR_EN;
input [PORT_B_WR_BE_WIDTH-1:0] PORT_B_WR_BE;
input PORT_B_CLK_EN;
output [PORT_B_WIDTH-1:0] PORT_B_RD_DATA;


// Fixed mode settings
localparam [ 0:0] SYNC_FIFO1_i  = 1'd0;
localparam [ 0:0] FMODE1_i      = 1'd0;
localparam [ 0:0] POWERDN1_i    = 1'd0;
localparam [ 0:0] SLEEP1_i      = 1'd0;
localparam [ 0:0] PROTECT1_i    = 1'd0;
localparam [11:0] UPAE1_i       = 12'd10;
localparam [11:0] UPAF1_i       = 12'd10;

localparam [ 0:0] SYNC_FIFO2_i  = 1'd0;
localparam [ 0:0] FMODE2_i      = 1'd0;
localparam [ 0:0] POWERDN2_i    = 1'd0;
localparam [ 0:0] SLEEP2_i      = 1'd0;
localparam [ 0:0] PROTECT2_i    = 1'd0;
localparam [10:0] UPAE2_i       = 11'd10;
localparam [10:0] UPAF2_i       = 11'd10;

// Width mode function
function [2:0] mode;
input integer width;
case (width)
1: mode = 3'b101;
2: mode = 3'b110;
4: mode = 3'b100;
8,9: mode = 3'b001;
16, 18: mode = 3'b010;
32, 36: mode = 3'b011;
default: mode = 3'b000;
endcase
endfunction

wire REN_A1_i;
wire REN_A2_i;

wire REN_B1_i;
wire REN_B2_i;

wire WEN_A1_i;
wire WEN_A2_i;

wire WEN_B1_i;
wire WEN_B2_i;

wire [1:0] BE_A1_i;
wire [1:0] BE_A2_i;

wire [1:0] BE_B1_i;
wire [1:0] BE_B2_i;

wire [14:0] ADDR_A1_i;
wire [13:0] ADDR_A2_i;

wire [14:0] ADDR_B1_i;
wire [13:0] ADDR_B2_i;

wire [17:0] WDATA_A1_i;
wire [17:0] WDATA_A2_i;

wire [17:0] WDATA_B1_i;
wire [17:0] WDATA_B2_i;

wire [17:0] RDATA_A1_o;
wire [17:0] RDATA_A2_o;

wire [17:0] RDATA_B1_o;
wire [17:0] RDATA_B2_o;


localparam [ 0:0] SPLIT_i       = 1'b0;

// Set port width mode (In non-split mode A2/B2 is not active. Set same values anyway to match previous behavior.)
localparam [ 2:0] RMODE_A1_i    = mode(PORT_A_WIDTH);
localparam [ 2:0] RMODE_B1_i    = mode(PORT_B_WIDTH);
localparam [ 2:0] WMODE_A1_i    = mode(PORT_A_WIDTH);
localparam [ 2:0] WMODE_B1_i    = mode(PORT_B_WIDTH);

localparam [ 2:0] RMODE_A2_i    = mode(PORT_A_WIDTH);
localparam [ 2:0] RMODE_B2_i    = mode(PORT_B_WIDTH);
localparam [ 2:0] WMODE_A2_i    = mode(PORT_A_WIDTH);
localparam [ 2:0] WMODE_B2_i    = mode(PORT_B_WIDTH);

assign REN_A1_i = PORT_A_CLK_EN;
assign WEN_A1_i = PORT_A_CLK_EN & PORT_A_WR_EN;
assign {BE_A2_i, BE_A1_i} = PORT_A_WR_BE;

assign REN_B1_i = PORT_B_CLK_EN;
assign WEN_B1_i = PORT_B_CLK_EN & PORT_B_WR_EN;
assign {BE_B2_i, BE_B1_i} = PORT_B_WR_BE;

case (PORT_A_WIDTH)
9: assign { WDATA_A1_i[16], WDATA_A1_i[7:0] } = PORT_A_WR_DATA;
18: assign { WDATA_A1_i[17], WDATA_A1_i[15:8], WDATA_A1_i[16], WDATA_A1_i[7:0] } = PORT_A_WR_DATA;
32: assign { WDATA_A2_i[15:0], WDATA_A1_i[15:0] } = PORT_A_WR_DATA;
36: assign { WDATA_A2_i[17], WDATA_A2_i[15:8], WDATA_A2_i[16], WDATA_A2_i[7:0], WDATA_A1_i[17], WDATA_A1_i[15:8], WDATA_A1_i[16], WDATA_A1_i[7:0]} = PORT_A_WR_DATA;
default: assign WDATA_A1_i = PORT_A_WR_DATA; // 1,2,4,8,16
endcase

case (PORT_B_WIDTH)
9: assign { WDATA_B1_i[16], WDATA_B1_i[7:0] } = PORT_B_WR_DATA;
18: assign { WDATA_B1_i[17], WDATA_B1_i[15:8], WDATA_B1_i[16], WDATA_B1_i[7:0] } = PORT_B_WR_DATA;
32: assign { WDATA_B2_i[15:0], WDATA_B1_i[15:0] } = PORT_B_WR_DATA;
36: assign { WDATA_B2_i[17], WDATA_B2_i[15:8], WDATA_B2_i[16], WDATA_B2_i[7:0], WDATA_B1_i[17], WDATA_B1_i[15:8], WDATA_B1_i[16], WDATA_B1_i[7:0]} = PORT_B_WR_DATA;
default: assign WDATA_B1_i = PORT_B_WR_DATA; // 1,2,4,8,16
endcase

case (PORT_A_WIDTH)
9: assign PORT_A_RD_DATA = { RDATA_A1_o[16], RDATA_A1_o[7:0] };
18: assign PORT_A_RD_DATA = { RDATA_A1_o[17], RDATA_A1_o[15:8], RDATA_A1_o[16], RDATA_A1_o[7:0] };
32: assign PORT_A_RD_DATA = { RDATA_A2_o[15:0], RDATA_A1_o[15:0] };
36: assign PORT_A_RD_DATA = { RDATA_A2_o[17], RDATA_A2_o[15:8], RDATA_A2_o[16], RDATA_A2_o[7:0], RDATA_A1_o[17], RDATA_A1_o[15:8], RDATA_A1_o[16], RDATA_A1_o[7:0]};
default: assign PORT_A_RD_DATA = RDATA_A1_o; // 1,2,4,8,16
endcase

case (PORT_B_WIDTH)
9: assign PORT_B_RD_DATA = { RDATA_B1_o[16], RDATA_B1_o[7:0] };
18: assign PORT_B_RD_DATA = { RDATA_B1_o[17], RDATA_B1_o[15:8], RDATA_B1_o[16], RDATA_B1_o[7:0] };
32: assign PORT_B_RD_DATA = { RDATA_B2_o[15:0], RDATA_B1_o[15:0] };
36: assign PORT_B_RD_DATA = { RDATA_B2_o[17], RDATA_B2_o[15:8], RDATA_B2_o[16], RDATA_B2_o[7:0], RDATA_B1_o[17], RDATA_B1_o[15:8], RDATA_B1_o[16], RDATA_B1_o[7:0]};
default: assign PORT_B_RD_DATA = RDATA_B1_o; // 1,2,4,8,16
endcase

defparam _TECHMAP_REPLACE_.MODE_BITS = { SPLIT_i,
			UPAF2_i, UPAE2_i, PROTECT2_i, SLEEP2_i, POWERDN2_i, FMODE2_i, WMODE_B2_i, WMODE_A2_i, RMODE_B2_i, RMODE_A2_i, SYNC_FIFO2_i,
			UPAF1_i, UPAE1_i, PROTECT1_i, SLEEP1_i, POWERDN1_i, FMODE1_i, WMODE_B1_i, WMODE_A1_i, RMODE_B1_i, RMODE_A1_i, SYNC_FIFO1_i
		};

(* is_inferred = 1 *)
TDP36K _TECHMAP_REPLACE_ (
	.RESET_ni(1'b1),
	.WDATA_A1_i(WDATA_A1_i),
	.WDATA_A2_i(WDATA_A2_i),
	.RDATA_A1_o(RDATA_A1_o),
	.RDATA_A2_o(RDATA_A2_o),
	.ADDR_A1_i(PORT_A_ADDR),
	.ADDR_A2_i(PORT_A_ADDR),
	.CLK_A1_i(PORT_A_CLK),
	.CLK_A2_i(PORT_A_CLK),
	.REN_A1_i(REN_A1_i),
	.REN_A2_i(REN_A1_i),
	.WEN_A1_i(WEN_A1_i),
	.WEN_A2_i(WEN_A1_i),
	.BE_A1_i(BE_A1_i),
	.BE_A2_i(BE_A2_i),

	.WDATA_B1_i(WDATA_B1_i),
	.WDATA_B2_i(WDATA_B2_i),
	.RDATA_B1_o(RDATA_B1_o),
	.RDATA_B2_o(RDATA_B2_o),
	.ADDR_B1_i(PORT_B_ADDR),
	.ADDR_B2_i(PORT_B_ADDR),
	.CLK_B1_i(PORT_B_CLK),
	.CLK_B2_i(PORT_B_CLK),
	.REN_B1_i(REN_B1_i),
	.REN_B2_i(REN_B1_i),
	.WEN_B1_i(WEN_B1_i),
	.WEN_B2_i(WEN_B1_i),
	.BE_B1_i(BE_B1_i),
	.BE_B2_i(BE_B2_i),

	.FLUSH1_i(1'b0),
	.FLUSH2_i(1'b0)
);

endmodule

module \$__QLF_BRAM18_SDP (...);

// parameter INIT = 0;

parameter PORT_B_WR_EN_WIDTH = 1;
parameter WIDTH = 1;

localparam ADDR_WIDTH = 14;

input CLK_C;

input [ADDR_WIDTH-1:0] PORT_A_ADDR;
input PORT_A_CLK;
input PORT_A_CLK_EN;
output [WIDTH-1:0] PORT_A_RD_DATA;

input [ADDR_WIDTH-1:0] PORT_B_ADDR;
input PORT_B_CLK;
input PORT_B_CLK_EN;
input [PORT_B_WR_EN_WIDTH-1:0] PORT_B_WR_EN;
input [WIDTH-1:0] PORT_B_WR_DATA;

(* is_inferred = 1 *)
$__QLF_FACTOR_BRAM18_SDP #(
	.CFG_DBITS(WIDTH),
	.CFG_ABITS(ADDR_WIDTH),
	.CFG_ENABLE_B(PORT_B_WR_EN_WIDTH)
) _TECHMAP_REPLACE_ (
	.CLK1(CLK_C),
	.A1EN(PORT_A_CLK_EN),
	.A1ADDR(PORT_A_ADDR),
	.A1DATA(PORT_A_RD_DATA),
	.B1EN(PORT_B_WR_EN),
	.B1ADDR(PORT_B_ADDR),
	.B1DATA(PORT_B_WR_DATA)
);

endmodule