#!/usr/bin/env python

from sys import exit
from os import mkdir, unlink
from os.path import isdir, isfile
from subprocess import call, Popen, PIPE
from lxml import etree, html

WPEN = "http://en.wikipedia.org/wiki/"
WPEL = "http://el.wikipedia.org/wiki/"

def die (msg):
    print "Error:", msg
    print "Aborting..."
    exit(1)

def html_to_text (html, txt):
    if not isfile(txt):
        ret = call(['html2text', '-o', txt, '-style', 'pretty', html])
        if ret != 0:
            die('Cannot convert ' + html + ' to text')

def count (file):
    p1 = Popen(['grep', '-v', '^[[:space:]]*$', file], stdout=PIPE)
    p2 = Popen(['wc'], stdin=p1.stdout, stdout=PIPE)
    p1.stdout.close()
    output = p2.communicate()[0]
    [lines, words, chars] = output.split()
    return (lines, words, chars)

def print_clear (file, g):
    with open(file, "rt") as f:
        printing = True
        n = 0
        for line in f:
            line = line.strip()
            n = n+1
            if line == "<pre>":
                if not printing:
                    raise Exception('Mismatched <pre> in {0}, line {1}'
                                    .format(file, n))
                printing = False
            if line != "" and printing:
                print >> g, line
            if line == "</pre>":
                if printing:
                    raise Exception('Mismatched </pre> in {0}, line {1}'
                                    .format(file, n))
                printing = True
    g.close()

def clear_count (file):
    p = Popen(['wc'], stdin=PIPE, stdout=PIPE)
    try:
        print_clear(file, p.stdin)
    except Exception as exn:
        p.terminate()
        die(exn.args[0])
    output = p.stdout.readline()
    [lines, words, chars] = output.split()
    return (lines, words, chars)

def clear_ascii_count (file):
    p1 = Popen(['iconv', '-f', 'utf8', '-c', '-t', 'ascii'],
               stdin=PIPE, stdout=PIPE, close_fds=True)
    p2 = Popen(['wc'], stdin=p1.stdout, stdout=PIPE, close_fds=True)
    p1.stdout.close()
    try:
        print_clear(file, p1.stdin)
    except Exception as exn:
        p1.terminate()
        p2.terminate()
        die(exn.args[0])
    output = p2.stdout.readline()
    [lines, words, chars] = output.split()
    return (lines, words, chars)

if not isdir("en"):
    mkdir("en")

with open("terms.txt", "rt") as f:
    for line in f:
        term = line.strip()
        print 'Term:', term
        # get the wikipedia page
        enhtml = 'en/{0}.html'.format(term)
        if not isfile(enhtml):
            enurl = WPEN + term
            ret = call(['wget', '-q', '-O', enhtml, enurl])
            if ret != 0:
                unlink(enhtml)
                die('Cannot get ' + enurl)
        # raw english text
        entxt = 'en/{0}.txt'.format(term)
        html_to_text(enhtml, entxt)
        (lines, words, chars) = count(entxt)
        print 'Raw text:', lines, 'lines,', words, 'words,', chars, 'chars.'
        # try to do some parsing
        languages = set()
        languages.add('en')
        with open(enhtml, "rt") as g:
            root = html.parse(g)
            for entry in root.xpath('//div[@id="p-lang"]//li'):
                interwiki = entry.get("class")
                if interwiki[0:10] == 'interwiki-':
                    lang = interwiki[10:]
                    languages.add(lang)
        # the set of supported languages
        print 'Languages:',
        for lang in languages:
            print lang,
        print
        if 'el' in languages:
            die('Term ' + term + ' has already been translated')
        # clear text
        enclr = 'en/{0}.clear.txt'.format(term)
        if isfile(enclr):
            (lines, words, chars) = clear_count(enclr)
            print 'Clear text:', lines, 'lines,', words, \
                  'words,', chars, 'chars.'
            (lines, words, chars) = clear_ascii_count(enclr)
            print 'ASCII text:', lines, 'lines,', words, \
                  'words,', chars, 'chars.'
            print 'words per line:', float(words) / float(lines)
        # next
        print 
