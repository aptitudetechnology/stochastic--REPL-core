-- Stochastic REPL Core Firmware for ELM11
-- Lua script for microcontroller REPL interface

-- Configuration
local UART_ID = 0  -- UART0
uart.setup(UART_ID, 115200, 8, uart.PARITY_NONE, uart.STOPBITS_1)

-- Stochastic registers (probabilities 0-255)
local reg_a = 128  -- 0.5
local reg_b = 64   -- 0.25
local reg_result = 0

-- Command buffer
local cmd_buffer = ""

function process_command(cmd)
    local tokens = {}
    for token in string.gmatch(cmd, "%S+") do
        table.insert(tokens, token)
    end

    if #tokens == 0 then return end

    local command = tokens[1]

    if command == "load" and #tokens == 3 then
        local reg = tokens[2]
        local value = tonumber(tokens[3])
        if reg == "a" and value then
            reg_a = value
            uart.write(UART_ID, "OK\n")
        elseif reg == "b" and value then
            reg_b = value
            uart.write(UART_ID, "OK\n")
        else
            uart.write(UART_ID, "Invalid register or value\n")
        end

    elseif command == "mul" then
        -- Send to FPGA and get result
        -- Placeholder: approximate multiplication
        reg_result = math.floor((reg_a * reg_b) / 255)
        uart.write(UART_ID, "OK\n")

    elseif command == "print" and #tokens == 2 then
        local reg = tokens[2]
        if reg == "a" then
            uart.write(UART_ID, string.format("%.3f\n", reg_a / 255.0))
        elseif reg == "b" then
            uart.write(UART_ID, string.format("%.3f\n", reg_b / 255.0))
        elseif reg == "r" then
            uart.write(UART_ID, string.format("%.3f\n", reg_result / 255.0))
        else
            uart.write(UART_ID, "Invalid register\n")
        end

    elseif command == "help" then
        uart.write(UART_ID, "Commands:\n")
        uart.write(UART_ID, "  load <reg> <value>  - Load value (0-255) into register a or b\n")
        uart.write(UART_ID, "  mul                 - Multiply a * b, store in result\n")
        uart.write(UART_ID, "  print <reg>         - Print register value (a, b, or r)\n")
        uart.write(UART_ID, "  help                - Show this help\n")

    else
        uart.write(UART_ID, "Unknown command. Type 'help' for commands.\n")
    end
end

-- UART receive callback
uart.on(UART_ID, "data", function(data)
    for i = 1, #data do
        local c = string.byte(data, i)
        if c == 13 or c == 10 then  -- CR or LF
            process_command(cmd_buffer)
            cmd_buffer = ""
            uart.write(UART_ID, "> ")
        else
            cmd_buffer = cmd_buffer .. string.char(c)
        end
    end
end)

function run_fft_analysis()
    uart.write(UART_ID, "Stochastic REPL Core v0.1\n")
    uart.write(UART_ID, "Commands: load <reg> <value>, mul, print <reg>, help\n")
    uart.write(UART_ID, "> ")
end