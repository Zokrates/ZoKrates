/* ***** BEGIN LICENSE BLOCK *****
 * Distributed under the BSD license:
 *
 * Copyright (c) 2019, Ajax.org B.V.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of Ajax.org B.V. nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL AJAX.ORG B.V. BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * ***** END LICENSE BLOCK ***** */

ace.define("ace/mode/zokrates_highlight_rules",["require","exports","module","ace/lib/oop","ace/mode/text_highlight_rules"], function(acequire, exports, module) {
    "use strict";

    var oop = acequire("../lib/oop");
    var TextHighlightRules = acequire("./text_highlight_rules").TextHighlightRules;

    var ZoKratesHighlightRules = function () {

        var keywords = (
            "assert|as|bool|byte|def|do|else|endfor|export|false|field|for|if|then|fi|import|from|in|private|public|return|struct|true|u8|u16|u32|u64"
        );

        var keywordMapper = this.createKeywordMapper({
            "keyword": keywords
        }, "identifier");

        var decimalInteger = "(?:(?:[1-9]\\d*)|(?:0))";
        var hexInteger = "(?:0[xX][\\dA-Fa-f]+)";
        var integer = "(?:" + decimalInteger + "|" + hexInteger + ")\\b";

        this.$rules = {
            "start": [
                {
                    token: "comment",  // single line comment
                    regex: "\\/\\/.*$"
                }, {
                    token: "comment",  // multi line comment
                    regex: "\\/\\*",
                    next: "comment"
                }, {
                    token: "string", // single line
                    regex: '["](?:(?:\\\\.)|(?:[^"\\\\]))*?["]'
                }, {
                    token: "constant.numeric", // integer
                    regex: integer
                }, {
                    token: keywordMapper,
                    regex: "[a-zA-Z_$][a-zA-Z0-9_$]*\\b"
                }, {
                    token: "keyword.operator",
                    regex: "\\+|\\-|\\*\\*?|\\/|\\|\\|?|&&?|\\^|!|<<?|>>?|<=|=>|==|!=|="
                }, {
                    token: "punctuation",
                    regex: ",|:|;"
                }, {
                    token: "lparen",
                    regex: "[[({]"
                }, {
                    token: "rparen",
                    regex: "[\\])}]"
                }, {
                    token: "text",
                    regex: "\\s+"
                }
            ],
            "comment": [
                {
                    token: "comment", // closing comment
                    regex: "\\*\\/",
                    next: "start"
                }, {
                    defaultToken: "comment"
                }
            ]
        };
    };

    oop.inherits(ZoKratesHighlightRules, TextHighlightRules);

    exports.ZoKratesHighlightRules = ZoKratesHighlightRules;
});

ace.define("ace/mode/zokrates",["require","exports","module","ace/lib/oop","ace/mode/text","ace/mode/zokrates_highlight_rules"], function(acequire, exports, module) {
    "use strict";

    var oop = acequire("../lib/oop");
    var TextMode = acequire("./text").Mode;
    var ZoKratesHighlightRules = acequire("./zokrates_highlight_rules").ZoKratesHighlightRules;

    var Mode = function () {
        this.HighlightRules = ZoKratesHighlightRules;
    };
    oop.inherits(Mode, TextMode);

    (function () {
        this.$id = "ace/mode/zokrates";
    }).call(Mode.prototype);

    exports.Mode = Mode;
});