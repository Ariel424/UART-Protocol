`timescale 1ns / 1ps

module uart_tb;

    localparam CLK_FREQ = 50000000;
    localparam BAUD_RATE = 115200;

    reg clk = 0;
    reg rst = 1;
    always #10 clk = ~clk; // 50 MHz clock

    reg tx_start;
    reg [7:0] tx_data;
    wire tx_line;

    uart_tx #(.CLK_FREQ(CLK_FREQ), .BAUD_RATE(BAUD_RATE))
    TX (
        .clk(clk),
        .rst(rst),
        .tx_start(tx_start),
        .data_in(tx_data),
        .tx(tx_line),
        .tx_busy()
    );

    wire [7:0] rx_data;
    wire rx_ready;

    uart_rx #(.CLK_FREQ(CLK_FREQ), .BAUD_RATE(BAUD_RATE))
    RX (
        .clk(clk),
        .rst(rst),
        .rx(tx_line),
        .data_out(rx_data),
        .rx_ready(rx_ready)
    );

    initial begin
        $display("UART Verification Start");
        #100 rst = 0;

        tx_data = 8'hA5;
        tx_start = 1;
        #20 tx_start = 0;

        wait(rx_ready);
        if (rx_data == 8'hA5)
            $display("PASS: Received = %h", rx_data);
        else
            $display("FAIL: Expected A5, got %h", rx_data);

        #200000;
        $finish;
    end

endmodule
