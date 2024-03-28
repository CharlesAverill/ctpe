import sys

print(sys.argv)

testing = sys.argv[1] == "test"

with open(sys.argv[2], "r") as file:
    lines = file.readlines()

outlines = []
for line in lines:
    if line.strip() == "STYLE_PLACEHOLDER":
        with open(sys.argv[3], "r") as file:
            outlines.extend(file.readlines())
    elif testing and line.strip() == '<h2 class="home"><a href="/ctpe/">Home</a></h2>':
        outlines.append('<h2 class="home"><a href="/">Home</a></h2>')
    elif testing and line.strip() == '<script src="/ctpe/highlight/highlight.min.js"></script>':
        outlines.append('<script src="/highlight/highlight.min.js"></script>')
    elif testing and line.strip() == '<link rel="stylesheet" href="/ctpe/highlight/styles/school-book.css">':
        outlines.append('<link rel="stylesheet" href="/highlight/styles/school-book.css">')
    else:
        outlines.append(line)

with open(sys.argv[4], "w") as file:
    file.writelines(outlines)
