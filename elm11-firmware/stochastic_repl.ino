// ELM11 Stochastic REPL Firmware
// Simple command-line interface for stochastic computing

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

// UART communication with FPGA (placeholder)
#define UART_TX_PIN 1
#define UART_RX_PIN 2

// Command buffer
#define CMD_BUFFER_SIZE 64
char cmd_buffer[CMD_BUFFER_SIZE];
int cmd_index = 0;

// Stochastic registers (store probabilities as 0-255)
uint8_t reg_a = 128;  // 0.5
uint8_t reg_b = 64;   // 0.25
uint8_t reg_result = 0;

// Function prototypes
void process_command(char* cmd);
void send_to_fpga(uint8_t prob_a, uint8_t prob_b, char operation);
uint8_t receive_from_fpga();

void setup() {
    // Initialize UART
    Serial.begin(115200);
    Serial.println("Stochastic REPL Core v0.1");
    Serial.println("Commands: load <reg> <value>, mul <dest> <src1> <src2>, print <reg>");
    Serial.print("> ");
}

void loop() {
    if (Serial.available()) {
        char c = Serial.read();

        if (c == '\n' || c == '\r') {
            cmd_buffer[cmd_index] = '\0';
            process_command(cmd_buffer);
            cmd_index = 0;
            Serial.print("> ");
        } else if (cmd_index < CMD_BUFFER_SIZE - 1) {
            cmd_buffer[cmd_index++] = c;
        }
    }
}

void process_command(char* cmd) {
    char* token = strtok(cmd, " ");

    if (strcmp(token, "load") == 0) {
        // load <reg> <value>
        token = strtok(NULL, " ");
        char reg = token[0];
        token = strtok(NULL, " ");
        uint8_t value = atoi(token);

        if (reg == 'a') reg_a = value;
        else if (reg == 'b') reg_b = value;

        Serial.println("OK");

    } else if (strcmp(token, "mul") == 0) {
        // mul <dest> <src1> <src2>
        // For now, assume dest is result, src1=a, src2=b
        send_to_fpga(reg_a, reg_b, 'm');  // 'm' for multiply
        reg_result = receive_from_fpga();
        Serial.println("OK");

    } else if (strcmp(token, "print") == 0) {
        // print <reg>
        token = strtok(NULL, " ");
        char reg = token[0];

        if (reg == 'a') Serial.println(reg_a / 255.0, 3);
        else if (reg == 'b') Serial.println(reg_b / 255.0, 3);
        else if (reg == 'r') Serial.println(reg_result / 255.0, 3);

    } else if (strcmp(token, "help") == 0) {
        Serial.println("Commands:");
        Serial.println("  load <reg> <value>  - Load value (0-255) into register a or b");
        Serial.println("  mul                 - Multiply a * b, store in result");
        Serial.println("  print <reg>         - Print register value (a, b, or r)");
        Serial.println("  help                - Show this help");

    } else {
        Serial.println("Unknown command. Type 'help' for commands.");
    }
}

// Placeholder functions for FPGA communication
void send_to_fpga(uint8_t prob_a, uint8_t prob_b, char operation) {
    // Send command to FPGA via UART or GPIO
    // Implementation depends on hardware interface
}

uint8_t receive_from_fpga() {
    // Receive result from FPGA
    // For now, return a dummy value
    return (reg_a * reg_b) / 255;  // Approximate multiplication
}