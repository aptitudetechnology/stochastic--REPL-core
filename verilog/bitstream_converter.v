`timescale 1ns / 1ps

// Bitstream to Binary Converter
// Counts 1's in bitstream to estimate probability
module bitstream_to_binary #(
    parameter BITSTREAM_LENGTH = 1024
)(
    input wire clk,
    input wire rst,
    input wire bitstream,
    input wire start_conversion,
    output reg [15:0] binary_value,  // 0-65535 representing 0.0-1.0
    output reg conversion_done
);

    reg [31:0] bit_count;
    reg [31:0] one_count;
    reg converting;

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            bit_count <= 0;
            one_count <= 0;
            converting <= 0;
            conversion_done <= 0;
            binary_value <= 0;
        end else if (start_conversion && !converting) begin
            // Start new conversion
            bit_count <= 0;
            one_count <= 0;
            converting <= 1;
            conversion_done <= 0;
        end else if (converting) begin
            if (bit_count < BITSTREAM_LENGTH) begin
                bit_count <= bit_count + 1;
                if (bitstream) begin
                    one_count <= one_count + 1;
                end
            end else begin
                // Conversion complete
                binary_value <= (one_count * 65535) / BITSTREAM_LENGTH;
                conversion_done <= 1;
                converting <= 0;
            end
        end else begin
            conversion_done <= 0;
        end
    end

endmodule