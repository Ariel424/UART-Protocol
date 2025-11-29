module uart_tx #
(
    parameter CLK_FREQ = 50000000,   // Hz
    parameter BAUD_RATE = 115200
)
(
    input  wire clk,
    input  wire rst,
    input  wire tx_start,
    input  wire [7:0] data_in,
    output reg  tx,
    output reg  tx_busy
);

    localparam BAUD_DIV = CLK_FREQ / BAUD_RATE;

    reg [15:0] baud_cnt = 0;
    reg baud_tick;

    always @(posedge clk) begin
        if (rst) begin
            baud_cnt <= 0;
            baud_tick <= 0;
        end else begin
            if (baud_cnt == BAUD_DIV-1) begin
                baud_cnt <= 0;
                baud_tick <= 1;
            end else begin
                baud_cnt <= baud_cnt + 1;
                baud_tick <= 0;
            end
        end
    end

    reg [3:0] bit_pos = 0;
    reg [9:0] shift_reg = 10'b1111111111;

    always @(posedge clk) begin
        if (rst) begin
            tx <= 1;
            tx_busy <= 0;
            bit_pos <= 0;
        end else begin
            if (tx_start && !tx_busy) begin
                shift_reg <= {1'b1, data_in, 1'b0}; 
                tx_busy   <= 1;
                bit_pos   <= 0;
            end else if (baud_tick && tx_busy) begin
                tx <= shift_reg[bit_pos];
                bit_pos <= bit_pos + 1;

                if (bit_pos == 9)
                    tx_busy <= 0;
            end
        end
    end

endmodule

