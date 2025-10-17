`timescale 1ns / 1ps

// Stochastic Number Generator (SNG)
// Converts binary input to stochastic bitstream
module stochastic_number_generator #(
    parameter SEED = 32'h12345678  // LFSR seed
)(
    input wire clk,
    input wire rst,
    input wire [7:0] probability,  // 0-255 representing 0.0-1.0
    output wire bitstream
);

    // 32-bit LFSR for pseudo-random generation
    reg [31:0] lfsr;
    wire feedback = lfsr[31] ^ lfsr[21] ^ lfsr[1] ^ lfsr[0];  // Fibonacci LFSR

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            lfsr <= SEED;
        end else begin
            lfsr <= {lfsr[30:0], feedback};
        end
    end

    // Compare LFSR output with probability threshold
    // Higher probability = more 1's in bitstream
    assign bitstream = (lfsr[7:0] < probability) ? 1'b1 : 1'b0;

endmodule