`timescale 1ns / 1ps

// Stochastic Scaled Adder
// Performs scaled addition using multiplexer
module stochastic_adder (
    input wire clk,
    input wire rst,
    input wire control_bitstream,  // P(control=1) = scaling factor
    input wire a_bitstream,
    input wire b_bitstream,
    output wire result_bitstream
);

    // MUX: if control=1, output a; else output b
    // P(result=1) = P(control=1)*P(a=1) + P(control=0)*P(b=1)
    assign result_bitstream = control_bitstream ? a_bitstream : b_bitstream;

endmodule