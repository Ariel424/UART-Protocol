module uart_rx #
(
    parameter CLK_FREQ = 50000000,
    parameter BAUD_RATE = 115200
)
(
    input  wire clk,
    input  wire rst,
    input  wire rx,
    output reg  [7:0] data_out,
    output reg  rx_ready
);

    localparam BAUD_DIV = CLK_FREQ / BAUD_RATE;
    localparam HALF_DIV = BAUD_DIV / 2;

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
    reg sampling = 0;
    reg [7:0] buffer;

    always @(posedge clk) begin
        if (rst) begin
            sampling <= 0;
            bit_pos <= 0;
            rx_ready <= 0;
        end else begin
            rx_ready <= 0;

            if (!sampling) begin
                if (!rx) begin
                    sampling <= 1;
                    baud_cnt <= HALF_DIV; // center of start bit
                    bit_pos <= 0;
                end
            end else begin
                if (baud_tick) begin
                    if (bit_pos < 8) begin
                        buffer[bit_pos] <= rx;
                        bit_pos <= bit_pos + 1;
                    end else begin
                        data_out <= buffer;
                        rx_ready <= 1;
                        sampling <= 0;
                    end
                end
            end
        end
    end

endmodule

