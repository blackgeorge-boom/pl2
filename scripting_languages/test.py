import urllib

url = 'http://localhost/gimmeabitcoin.php'

f = urllib.urlopen(url)
myfile = f.read()

lines = myfile.splitlines()
for line in lines:
    line = line.lstrip()
    tokens = line.split()
    if (line.startswith("<span class=\"question\">")):
        print (tokens[5])[0:4]
