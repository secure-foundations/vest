/* Keep this grammar in sync with vest/src/vest.pest and vest/vest.vim. */
(function () {
  "use strict";

  var forbiddenRustKeywords =
    "as async await break continue crate dyn else extern false fn for if impl in " +
    "let loop match mod move mut pub ref return self Self static struct super trait " +
    "true type unsafe use where while abstract become box do final override priv try " +
    "typeof unsized virtual yield";

  hljs.registerLanguage("vest", function (hljs) {
    var todo = {
      className: "doctag",
      begin: /\b(?:TODO|FIXME|XXX|NOTE)\b/,
    };

    var lineComment = {
      className: "comment",
      begin: /\/\//,
      end: /$/,
      contains: [todo],
    };

    var string = {
      className: "string",
      begin: /"/,
      end: /"/,
      illegal: /\n/,
      contains: [hljs.BACKSLASH_ESCAPE],
    };

    var character = {
      className: "string",
      begin: /'(?:\\x[0-9A-Fa-f]{2}|[^'\n])'/,
      relevance: 0,
    };

    var number = {
      className: "number",
      relevance: 0,
      variants: [
        { begin: /\b0x[0-9A-Fa-f]+(?:[ui][0-9]+)?\b/ },
        { begin: /\b[0-9]+(?:[ui][0-9]+)?\b/ },
      ],
    };

    return {
      name: "Vest",
      aliases: ["vest"],
      keywords: {
        $pattern: /[A-Za-z_][A-Za-z0-9_]*/,
        keyword: "macro const enum choose wrap bits",
        type: "Option Vec Tail Nothing Never btc_varint uleb128",
      },
      contains: [
        // Put comments and strings before punctuation that can open them.
        lineComment,
        string,
        character,
        {
          className: "meta",
          begin: /!(?:LITTLE|BIG)_ENDIAN\b/,
        },
        {
          className: "variable",
          begin: /@[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*/,
        },
        {
          className: "meta",
          begin: /\b[A-Za-z_][A-Za-z0-9_]*(?=!\s*\()/,
        },
        {
          className: "title",
          begin: /^[A-Za-z_][A-Za-z0-9_]*(?=\s*(?:\([^)]*\))?\s*=)/m,
        },
        {
          className: "symbol",
          begin: /\b_\b/,
          relevance: 0,
        },
        {
          className: "type",
          begin: /\b[ui][0-9]+\b/,
          relevance: 0,
        },
        number,
        {
          className: "meta",
          begin: /\|\s*(?:[A-Za-z_][A-Za-z0-9_]*|[ui][0-9]+|btc_varint|uleb128)\s*\|/,
          relevance: 0,
        },
        {
          className: "operator",
          begin: />>=|=>|\.\.\.|\.\./,
          relevance: 0,
        },
        {
          className: "punctuation",
          begin: /[\[\]{}()<>,;:=|!+*/-]/,
          relevance: 0,
        },
        {
          className: "deletion",
          begin: new RegExp("\\b(?:" + forbiddenRustKeywords.split(" ").join("|") + ")\\b"),
          relevance: 0,
        },
      ],
    };
  });

  // mdBook loads additional scripts after book.js. Its first highlighting pass
  // therefore sees `vest` as unknown; run the Vest blocks again now that the
  // language is registered.
  if (typeof document !== "undefined") {
    Array.prototype.forEach.call(
      document.querySelectorAll("code.language-vest"),
      function (block) {
        hljs.highlightBlock(block);
      }
    );
  }
})();
