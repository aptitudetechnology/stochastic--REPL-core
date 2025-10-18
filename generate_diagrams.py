#!/usr/bin/env python3
"""
Mermaid Diagram Generator for Stochastic Computing Hardware Documentation

This script extracts Mermaid syntax from photo-desc.md and generates SVG/PNG diagrams.
Requires mermaid-cli to be installed: npm install -g @mermaid-js/mermaid-cli

Usage:
    python generate_diagrams.py [--format svg|png] [--output-dir ./diagrams]

Dependencies:
    - mermaid-cli (npm install -g @mermaid-js/mermaid-cli)
    - Python 3.6+
"""

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import List, Tuple, Optional


class MermaidGenerator:
    def __init__(self, output_dir: str = "./diagrams", format_type: str = "svg"):
        self.output_dir = Path(output_dir)
        self.format_type = format_type
        self.output_dir.mkdir(exist_ok=True)

    def extract_mermaid_blocks(self, markdown_file: str) -> List[Tuple[str, str, int]]:
        """
        Extract Mermaid code blocks from markdown file.
        Returns list of tuples: (title, mermaid_code, line_number)
        """
        with open(markdown_file, 'r', encoding='utf-8') as f:
            content = f.read()

        # Split content into lines for better processing
        lines = content.split('\n')
        mermaid_blocks = []
        current_title = ""

        i = 0
        while i < len(lines):
            line = lines[i].strip()

            # Look for section headers (## Title)
            if line.startswith('## '):
                current_title = line[3:].strip()

            # Look for mermaid code block start
            if line == '```mermaid':
                # Found start of mermaid block
                mermaid_lines = []
                block_start_line = i + 1  # Line number where mermaid code starts
                i += 1  # Skip the ```mermaid line

                # Collect all lines until closing ```
                while i < len(lines) and lines[i].strip() != '```':
                    mermaid_lines.append(lines[i])
                    i += 1

                if i < len(lines):  # Found closing ```
                    mermaid_code = '\n'.join(mermaid_lines).strip()

                    # Clean up the title
                    clean_title = current_title if current_title else f"diagram_{len(mermaid_blocks)+1}"

                    # Replace spaces and special chars in filename
                    filename = re.sub(r'[^\w\-_]', '_', clean_title.lower())
                    filename = re.sub(r'_+', '_', filename).strip('_')

                    mermaid_blocks.append((filename, mermaid_code, block_start_line))

                    # Reset title for next block
                    current_title = ""

            i += 1

        return mermaid_blocks

    def generate_diagram(self, mermaid_code: str, output_path: Path) -> bool:
        """
        Generate a diagram from Mermaid code using mermaid-cli.
        """
        try:
            # Create a temporary file for the Mermaid code
            temp_file = output_path.with_suffix('.mmd')
            with open(temp_file, 'w', encoding='utf-8') as f:
                f.write(mermaid_code)

            # Run mermaid-cli to generate the diagram
            cmd = [
                'mmdc',
                '-i', str(temp_file),
                '-o', str(output_path),
                '-t', 'default',  # theme
                '-b', 'transparent'  # background
            ]

            if self.format_type == 'png':
                cmd.extend(['-w', '1200', '-H', '800'])  # width and height for PNG

            result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)

            # Clean up temp file
            temp_file.unlink(missing_ok=True)

            if result.returncode == 0:
                print(f"✓ Generated {output_path}")
                return True
            else:
                print(f"✗ Failed to generate {output_path}")
                print(f"Error: {result.stderr}")
                return False

        except subprocess.TimeoutExpired:
            print(f"✗ Timeout generating {output_path}")
            return False
        except Exception as e:
            print(f"✗ Error generating {output_path}: {e}")
            return False

    def generate_html_gallery(self, diagrams: List[Tuple[str, str, int]]) -> None:
        """
        Generate an HTML gallery showing all diagrams.
        """
        html_path = self.output_dir / "diagram_gallery.html"

        html_content = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Stochastic Computing Hardware Diagrams</title>
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
            background: #f5f5f5;
        }}
        .diagram-container {{
            background: white;
            border-radius: 8px;
            padding: 20px;
            margin: 20px 0;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        .diagram-title {{
            color: #2c3e50;
            border-bottom: 2px solid #3498db;
            padding-bottom: 10px;
            margin-bottom: 20px;
        }}
        .diagram {{
            text-align: center;
            max-width: 100%;
            height: auto;
        }}
        .diagram img {{
            max-width: 100%;
            height: auto;
            border: 1px solid #ddd;
            border-radius: 4px;
        }}
        .stats {{
            background: #ecf0f1;
            padding: 15px;
            border-radius: 4px;
            margin-top: 20px;
        }}
        h1 {{
            color: #2c3e50;
            text-align: center;
        }}
    </style>
</head>
<body>
    <h1>Stochastic Computing Hardware Diagrams</h1>
    <p>Generated diagrams from photo-desc.md Mermaid syntax</p>

    <div class="stats">
        <strong>Total Diagrams:</strong> {len(diagrams)}<br>
        <strong>Format:</strong> {self.format_type.upper()}<br>
        <strong>Generated:</strong> {os.popen('date').read().strip()}
    </div>
"""

        for filename, _, line_num in diagrams:
            diagram_path = f"{filename}.{self.format_type}"
            html_content += f"""
    <div class="diagram-container">
        <h2 class="diagram-title">{filename.replace('_', ' ').title()}</h2>
        <div class="diagram">
            <img src="{diagram_path}" alt="{filename}" loading="lazy">
        </div>
        <p><em>Line {line_num} in photo-desc.md</em></p>
    </div>
"""

        html_content += """
</body>
</html>
"""

        with open(html_path, 'w', encoding='utf-8') as f:
            f.write(html_content)

        print(f"✓ Generated HTML gallery: {html_path}")

    def check_dependencies(self) -> bool:
        """
        Check if mermaid-cli is installed.
        """
        try:
            result = subprocess.run(['mmdc', '--version'],
                                  capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                print(f"✓ mermaid-cli found: {result.stdout.strip()}")
                return True
            else:
                print("✗ mermaid-cli not found")
                return False
        except (subprocess.CalledProcessError, FileNotFoundError):
            print("✗ mermaid-cli not found")
            print("\nInstall with: npm install -g @mermaid-js/mermaid-cli")
            return False

    def process_markdown_file(self, markdown_file: str) -> None:
        """
        Main processing function.
        """
        if not self.check_dependencies():
            sys.exit(1)

        if not os.path.exists(markdown_file):
            print(f"✗ Markdown file not found: {markdown_file}")
            sys.exit(1)

        print(f"Processing {markdown_file}...")

        # Extract Mermaid blocks
        mermaid_blocks = self.extract_mermaid_blocks(markdown_file)

        if not mermaid_blocks:
            print("✗ No Mermaid blocks found in the file")
            return

        print(f"Found {len(mermaid_blocks)} Mermaid diagrams")

        # Generate diagrams
        successful = 0
        for filename, code, line_num in mermaid_blocks:
            output_path = self.output_dir / f"{filename}.{self.format_type}"
            if self.generate_diagram(code, output_path):
                successful += 1

        print(f"\nGenerated {successful}/{len(mermaid_blocks)} diagrams")

        # Generate HTML gallery
        if successful > 0:
            self.generate_html_gallery(mermaid_blocks)


def main():
    parser = argparse.ArgumentParser(
        description="Generate diagrams from Mermaid syntax in markdown files"
    )
    parser.add_argument(
        "--input", "-i",
        default="lsi/photo-desc.md",
        help="Input markdown file (default: lsi/photo-desc.md)"
    )
    parser.add_argument(
        "--output-dir", "-o",
        default="./diagrams",
        help="Output directory for diagrams (default: ./diagrams)"
    )
    parser.add_argument(
        "--format", "-f",
        choices=["svg", "png"],
        default="svg",
        help="Output format (default: svg)"
    )

    args = parser.parse_args()

    generator = MermaidGenerator(args.output_dir, args.format)
    generator.process_markdown_file(args.input)


if __name__ == "__main__":
    main()