`timescale 1ns / 1ps

module tb_stochastic_repl_core;

    reg clk;
    reg rst;
    wire uart_rx;
    wire uart_tx;
    wire led_busy;
    wire led_error;

    // Instantiate the core
    stochastic_repl_core dut (
        .clk(clk),
        .rst(rst),
        .uart_rx(uart_rx),
        .uart_tx(uart_tx),
        .led_busy(led_busy),
        .led_error(led_error)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end

    // Test stimulus
    initial begin
        // Reset
        rst = 1;
        #100;
        rst = 0;

        // Run for some time to generate bitstreams
        #1000000;  // 1ms

        $finish;
    end

    // Monitor
    initial begin
        $monitor("Time: %t, Busy: %b, Error: %b", $time, led_busy, led_error);
    end

endmodule