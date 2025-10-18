# Mermaid Diagram Generator

This Python script extracts Mermaid syntax from `photo-desc.md` and generates SVG/PNG diagrams for the stochastic computing hardware documentation.

## Installation

### 1. Install Node.js and npm (if not already installed)
```bash
# Ubuntu/Debian
sudo apt update
sudo apt install nodejs npm

# Or install Node.js via NodeSource repository for latest version
curl -fsSL https://deb.nodesource.com/setup_18.x | sudo -E bash -
sudo apt-get install -y nodejs
```

### 2. Install Mermaid CLI
```bash
npm install -g @mermaid-js/mermaid-cli
```

### 3. Verify installation
```bash
mmdc --version
```

## Usage

### Basic usage (generate SVG diagrams)
```bash
python3 generate_diagrams.py
```

### Generate PNG diagrams
```bash
python3 generate_diagrams.py --format png
```

### Custom input/output
```bash
python3 generate_diagrams.py --input lsi/photo-desc.md --output-dir ./my-diagrams --format svg
```

### Command line options
- `--input, -i`: Input markdown file (default: `lsi/photo-desc.md`)
- `--output-dir, -o`: Output directory (default: `./diagrams`)
- `--format, -f`: Output format - `svg` or `png` (default: `svg`)

## Output

The script generates:
1. Individual diagram files (`.svg` or `.png`) in the output directory
2. An HTML gallery (`diagram_gallery.html`) for easy viewing of all diagrams

## Features

- Extracts all Mermaid code blocks from markdown files
- Generates clean, professional diagrams
- Creates an HTML gallery for easy browsing
- Supports both SVG and PNG output formats
- Automatic filename generation from section titles
- Error handling and progress reporting

## Dependencies

- Python 3.6+
- Node.js and npm
- @mermaid-js/mermaid-cli

## Troubleshooting

### "mermaid-cli not found"
Make sure you've installed mermaid-cli globally:
```bash
npm install -g @mermaid-js/mermaid-cli
```

### Permission issues
If you get permission errors, try:
```bash
sudo npm install -g @mermaid-js/mermaid-cli
```

### Puppeteer issues (common with mermaid-cli)
If diagrams fail to generate, you might need to install additional dependencies:
```bash
sudo apt-get install -y ca-certificates fonts-liberation libappindicator3-1 libasound2 libatk-bridge2.0-0 libatk1.0-0 libc6 libcairo2 libcups2 libdbus-1-3 libexpat1 libfontconfig1 libgbm1 libgcc1 libglib2.0-0 libgtk-3-0 libnspr4 libnss3 libpango-1.0-0 libpangoft2-1.0-0 libstdc++6 libx11-6 libx11-xcb1 libxcb1 libxcomposite1 libxcursor1 libxdamage1 libxext6 libxfixes3 libxi6 libxrandr2 libxrender1 libxss1 libxtst6 lsb-release wget xdg-utils
```

## Example Output

After running the script, you'll get:
```
diagrams/
├── system_block_diagram.svg
├── power_distribution_setup.svg
├── elm11_board_placement.svg
├── tang_nano_fpga_connections.svg
├── level_shifter_installation.svg
├── gpio_pin_mapping_summary.svg
├── complete_system_wiring_flow.svg
└── diagram_gallery.html
```