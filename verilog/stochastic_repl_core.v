`timescale 1ns / 1ps

// Stochastic REPL Core Top Module
module stochastic_repl_core (
    input wire clk,
    input wire rst,
    // UART interface for REPL commands
    input wire uart_rx,
    output wire uart_tx,
    // Status LEDs
    output wire led_busy,
    output wire led_error
);

    // Internal signals
    wire [7:0] prob_a, prob_b, prob_control;
    wire bitstream_a, bitstream_b, bitstream_control;
    wire result_bitstream;
    wire [15:0] result_binary;
    wire conversion_done;

    // Command parser (simplified - would parse UART commands)
    reg [7:0] cmd_prob_a = 128;  // 0.5
    reg [7:0] cmd_prob_b = 64;   // 0.25
    reg [7:0] cmd_prob_control = 128;  // 0.5
    reg cmd_start_conversion = 0;

    // SNG instances
    stochastic_number_generator sng_a (
        .clk(clk),
        .rst(rst),
        .probability(cmd_prob_a),
        .bitstream(bitstream_a)
    );

    stochastic_number_generator sng_b (
        .clk(clk),
        .rst(rst),
        .probability(cmd_prob_b),
        .bitstream(bitstream_b)
    );

    stochastic_number_generator sng_control (
        .clk(clk),
        .rst(rst),
        .probability(cmd_prob_control),
        .bitstream(bitstream_control)
    );

    // Arithmetic units
    stochastic_multiplier mult (
        .clk(clk),
        .rst(rst),
        .a_bitstream(bitstream_a),
        .b_bitstream(bitstream_b),
        .result_bitstream(result_bitstream)
    );

    // For now, use multiplier output directly
    // Could add adder or other operations

    // Converter
    bitstream_to_binary converter (
        .clk(clk),
        .rst(rst),
        .bitstream(result_bitstream),
        .start_conversion(cmd_start_conversion),
        .binary_value(result_binary),
        .conversion_done(conversion_done)
    );

    // Status
    assign led_busy = cmd_start_conversion;
    assign led_error = 0;  // No error handling yet

    // UART (placeholder - would implement UART transmitter)
    assign uart_tx = 1'b1;  // Idle high

endmodule