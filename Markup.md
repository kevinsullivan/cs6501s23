# Markup directives

- main_mode = regex.compile(r'-- EXAMPLES:.*|/- EXAMPLES:.*|EXAMPLES: -/.*')
- both_mode = regex.compile(r'-- BOTH:.*|/- BOTH:.*|BOTH: -/.*')
- solutions_mode = regex.compile(r'-- SOLUTIONS:.*|/- SOLUTIONS:.*|SOLUTIONS: -/.*')
- omit_mode = regex.compile(r'-- OMIT:.*|/- OMIT:.*|OMIT: -/.*')
- tag_line = regex.compile(r'-- TAG:.*')
- text_start = regex.compile(r'/- TEXT:.*')
- text_end = regex.compile(r'TEXT\. -/.*')
- quote_start = regex.compile(r'-- QUOTE:.*')
- quote_end = regex.compile(r'-- QUOTE\..*')
- literalinclude = regex.compile(r'-- LITERALINCLUDE: (.*)')