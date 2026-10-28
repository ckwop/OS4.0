#!/usr/bin/env python3
"""Check that the course and the code tours still match the code.

The lectures in docs/course quote and name real code, and the tours in .tours
point into it; this fails when the code has moved on without them:
  data-ref="FILE"        FILE exists
  data-ref="FILE:WORD"   ... and defines WORD (a Forth definition, or an
                         assembly defcode, defconst or label)
  <pre data-src="FILE">  every line of the excerpt is a line of FILE (spacing
                         aside); a line starting with "…" stands for lines
                         left out, and may say what they do
  data-code="N"          on a slide: step N exists in the tour <body data-tour>
                         names, which the slide's Code button opens
  .tours/*.tour          each step's file exists, and its pattern matches it
                         (multiline, as CodeTour matches: ^ starts a line)

Usage: check-course.py   (from the repository root; make check-course)
"""

import glob
import html
import json
import os
import re
import sys

DEFINERS = r"(?::|constant|2constant|variable|create|user|value|defer|task|semaphore|wordlist constant|\d+ user-cells)"


def defines(text, path, word):
    w = re.escape(word)
    if path.endswith(".s"):
        return re.search(rf'def(?:code|const|var|word)\s+"{w}"|^{w}:', text, re.M) is not None
    return re.search(rf"(?:^|\s){DEFINERS}\s+{w}(?:\s|$)", text, re.M | re.I) is not None


def squash(line):
    return " ".join(line.split())


def check_lecture(path, problems):
    page = open(path, encoding="utf-8").read()
    where = os.path.relpath(path)
    for ref in re.findall(r'data-ref="([^"]+)"', page):
        file, _, word = ref.partition(":")
        if not os.path.isfile(file):
            problems.append(f"{where}: {file} does not exist")
        elif word and not defines(open(file, encoding="utf-8").read(), file, word):
            problems.append(f"{where}: {file} no longer defines {word}")
    tour = re.search(r'<body[^>]*data-tour="([^"]+)"', page)
    steps = re.findall(r'<section[^>]*data-code="(\d+)"', page)
    if tour:
        tour_path = f".tours/{tour.group(1)}.tour"
        if not os.path.isfile(tour_path):
            problems.append(f"{where}: {tour_path} does not exist")
        else:
            count = len(json.load(open(tour_path, encoding="utf-8")).get("steps", []))
            for step in steps:
                if not 1 <= int(step) <= count:
                    problems.append(f"{where}: data-code={step}, but {tour_path} has {count} steps")
    elif steps:
        problems.append(f"{where}: slides name tour steps, but <body> names no data-tour")
    for file, body in re.findall(r'<pre[^>]*data-src="([^"]+)"[^>]*>(.*?)</pre>', page, re.S):
        if not os.path.isfile(file):
            problems.append(f"{where}: {file} does not exist")
            continue
        lines = {squash(l) for l in open(file, encoding="utf-8").read().splitlines()}
        for line in html.unescape(re.sub(r"<[^>]+>", "", body)).splitlines():
            if squash(line) and not squash(line).startswith("…") and squash(line) not in lines:
                problems.append(f"{where}: excerpt line not in {file}: {line.strip()!r}")


def check_tour(path, problems):
    where = os.path.relpath(path)
    tour = json.load(open(path, encoding="utf-8"))
    for n, step in enumerate(tour.get("steps", []), 1):
        file = step.get("file")
        if not file:
            continue
        if not os.path.isfile(file):
            problems.append(f"{where} step {n}: {file} does not exist")
        elif "pattern" in step and not re.search(step["pattern"], open(file, encoding="utf-8").read(), re.M):
            problems.append(f"{where} step {n}: pattern {step['pattern']!r} not found in {file}")


def main():
    problems = []
    lectures = sorted(glob.glob("docs/course/*.html"))
    tours = sorted(glob.glob(".tours/*.tour"))
    for path in lectures:
        check_lecture(path, problems)
    for path in tours:
        check_tour(path, problems)
    for problem in problems:
        print(problem)
    print(f"course: {len(lectures)} pages, {len(tours)} tours, {len(problems)} problems")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
