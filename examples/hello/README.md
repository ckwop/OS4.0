# hello

The example OS 4.0 application. It greets whoever connects to TCP port 5000, counting them, then hangs up. It stands in for an app in a repository of its own: it builds against a tagged `os4` image of the base, never the base's source.

- [app.fs](app.fs) is the entry point. It includes [greeting.fs](greeting.fs), and its `main` starts the greeter task.
- [tests/hello.in](tests/hello.in) is a transcript test. A network peer connects to port 5000 and reports what it was sent ([tests/hello.peer](tests/hello.peer)).

From this directory, with the image built from the base (`docker build -t os4:0.10 -t os4 .` there):

```powershell
docker run --rm -v "${PWD}:/app" -w /app os4:0.10 os4-app test
docker run --rm -it -p 127.0.0.1:5000:5000 -v "${PWD}:/app" -w /app os4:0.10 os4-app run . 5000
```

While it runs, `telnet localhost 5000` gets the greeting.
