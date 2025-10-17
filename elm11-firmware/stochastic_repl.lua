-- Stochastic REPL Core Firmware for ELM11
-- Lua script for microcontroller REPL interface

-- UART setup (assuming ELM11 has serial interface)
local uart_id = 0  -- UART0
uart.setup(uart_id, 115200, 8, uart.PARITY_NONE, uart.STOPBITS_1)

-- Stochastic registers (probabilities 0-255)
local reg_a = 128  -- 0.5
local reg_b = 64   -- 0.25
local reg_result = 0

-- Command buffer
local cmd_buffer = ""
local cmd_index = 0

print("Stochastic REPL Core v0.1")
print("Commands: load <reg> <value>, mul, print <reg>, help")

-- UART receive callback
uart.on(uart_id, "data", function(data)
    for i = 1, #data do
        local c = string.byte(data, i)
        if c == 13 or c == 10 then  -- CR or LF
            process_command(cmd_buffer)
            cmd_buffer = ""
            uart.write(uart_id, "> ")
        else
            cmd_buffer = cmd_buffer .. string.char(c)
        end
    end
end)

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
        if reg == "a" then
            reg_a = value
            print("OK")
        elseif reg == "b" then
            reg_b = value
            print("OK")
        else
            print("Invalid register")
        end

    elseif command == "mul" then
        -- Send to FPGA and get result
        -- Placeholder: approximate multiplication
        reg_result = math.floor((reg_a * reg_b) / 255)
        print("OK")

    elseif command == "print" and #tokens == 2 then
        local reg = tokens[2]
        if reg == "a" then
            print(string.format("%.3f", reg_a / 255.0))
        elseif reg == "b" then
            print(string.format("%.3f", reg_b / 255.0))
        elseif reg == "r" then
            print(string.format("%.3f", reg_result / 255.0))
        else
            print("Invalid register")
        end

    elseif command == "help" then
        print("Commands:")
        print("  load <reg> <value>  - Load value (0-255) into register a or b")
        print("  mul                 - Multiply a * b, store in result")
        print("  print <reg>         - Print register value (a, b, or r)")
        print("  help                - Show this help")

    else
        print("Unknown command. Type 'help' for commands.")
    end
end

-- Send initial prompt
uart.write(uart_id, "> ")