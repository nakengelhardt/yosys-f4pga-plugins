`include "params.vh"

module top(clk_a, clk_b, a_a, rd_a, wd_a, we_a, a_b, rd_b, wd_b, we_b);

input wire clk_a;
input wire clk_b;

input wire [ABITS_A-1:0] a_a;
output reg [DBITS_A-1:0] rd_a;
input wire [DBITS_A-1:0] wd_a;
input wire we_a;
input wire [ABITS_B-1:0] a_b;
output reg [DBITS_B-1:0] rd_b;
input wire [DBITS_B-1:0] wd_b;
input wire we_b;

(* syn_ramstyle = "block_ram" *)
reg [DBITS_A-1:0] mem [0:DEPTH-1];

always @(posedge clk_a) begin
	if(we_a) begin
		mem[a_a] <= wd_a;
	end
	rd_a <= mem[a_a];
	if (we_b && a_b == a_a) rd_a <= 'x;

end

always @(posedge clk_b) begin
	if(we_b) begin
		mem[a_b] <= wd_b;
	end
	rd_b <= mem[a_b];
	if (we_a && a_b == a_a) rd_b <= 'x;
end

endmodule