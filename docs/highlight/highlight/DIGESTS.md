## Subresource Integrity

If you are loading Highlight.js via CDN you may wish to use [Subresource Integrity](https://developer.mozilla.org/en-US/docs/Web/Security/Subresource_Integrity) to guarantee that you are using a legimitate build of the library.

To do this you simply need to add the `integrity` attribute for each JavaScript file you download via CDN. These digests are used by the browser to confirm the files downloaded have not been modified.

```html
<script
  src="//cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/highlight.min.js"
  integrity="sha384-9mu2JKpUImscOMmwjm1y6MA2YsW3amSoFNYwKeUHxaXYKQ1naywWmamEGMdviEen"></script>
<!-- including any other grammars you might need to load -->
<script
  src="//cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/languages/go.min.js"
  integrity="sha384-WmGkHEmwSI19EhTfO1nrSk3RziUQKRWg3vO0Ur3VYZjWvJRdRnX4/scQg+S2w1fI"></script>
```

The full list of digests for every file can be found below.

### Digests

```
sha384-GKjp3Sn3AqyzCb5mF/Nnvs6KSMJUafdTv/3KlgvFf6B4LIXy7NeMoumvPeWDZnBs /es/languages/coq.js
sha384-i0H6klsviL0Lu3a5kZ6m/YXMTe2LYJ+I6ZKAsrDhhe4Xl7SvhKEfenOaZJwrBvPa /es/languages/coq.min.js
sha384-lO7lnocnwTUS5n56Ha8hDFE/66823d1EVQeImdX3RxEGZtgTxZF/ZmJ0cWY4gy3v /languages/coq.js
sha384-Djexk3CUuWlhu8etDgJrIqYyX/2iPKHlyqZo1l0uTRocpX+lFlDpNq4J8YaLd85M /languages/coq.min.js
sha384-gUv7nqPSGagrB36Y9uAAwBH1WNyxvaJncRNaeNUsSI5Yy3sgQumlGTHqEdP3Hzr1 /highlight.js
sha384-RZhN8uaX1AaoLo/PU/1hZ4ESceW011mmMzLlsqdpZqx5sgHxCDHrZIKKbtoEoGv+ /highlight.min.js
```

