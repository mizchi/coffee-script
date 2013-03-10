# The CoffeeScript Lexer. Uses a series of token-matching regexes to attempt
# matches against the beginning of the source code. When a match is found,
# a token is produced, we consume the match, and start again. Tokens are in the
# form:
#
#     [tag, value, locationData]
#
# where locationData is {first_line, first_column, last_line, last_column}, which is a
# format that can be fed directly into [Jison](http://github.com/zaach/jison).  These
# are read by jison in the `parser.lexer` function defined in coffee-script.coffee.


{Rewriter, INVERSES} = require './rewriter'

# Import the helpers we need.
{count, starts, compact, last, invertLiterate, locationDataToString} = require './helpers'

# The Lexer Class
# ---------------

# The Lexer class reads a stream of CoffeeScript and divvies it up into tagged
# tokens. Some potential ambiguity in the grammar has been avoided by
# pushing some extra smarts into the Lexer.
exports.Lexer = class Lexer

  # **tokenize** is the Lexer's main method. Scan by attempting to match tokens
  # one at a time, using a regular expression anchored at the start of the
  # remaining code, or a custom recursive token-matching method
  # (for interpolations). When the next token has been recorded, we move forward
  # within the code past the token, and begin again.
  #
  # Each tokenizing method is responsible for returning the number of characters
  # it has consumed.
  #
  # Before returning the token stream, run it through the [Rewriter](rewriter.html)
  # unless explicitly asked not to.
  tokenize: (code, opts = {}) ->
    # literate-mode かどうかのフラグ
    @literate = opts.literate  # Are we lexing literate CoffeeScript?
    # 現在のインデントレベル
    @indent   = 0              # The current indentation level.
    # インデントが無視されたブロックの中での現在のインデントレベル？
    # おそらく """　や ### や [ ] の宣言の中でインデントを無視する構文からの回復で使われる
    @indebt   = 0              # The over-indentation at the current level.
    # インデントが無視されたブロックで、いくつ無視しているか
    @outdebt  = 0              # The under-outdentation at the current level.
    @indents  = []             # The stack of all current indentation levels.
    # 現在のインデント階層
    @ends     = []             # The stack for pairing up tokens.
    # 現在の括弧()の深さ？
    @tokens   = []             # Stream of parsed tokens in the form `['TYPE', value, line]`.
    # Tokenのストリーム

    # 現在チャンクの開始列の深さ
    @chunkLine =
        opts.line or 0         # The start line for the current @chunk.

    # 現在チャンクの開始行
    @chunkColumn =
        opts.column or 0       # The start column of the current @chunk.

    # 末尾スペースを消したりliterateなmarkdownを消して下準備
    code = @clean code         # The stripped, cleaned original source code.

    # At every position, run through this list of attempted matches,
    # short-circuiting if any of them succeed. Their order determines precedence:
    # `@literalToken` is the fallback catch-all.

    # どの位置でも、これらのマッチを試みるリストから走らせ、もしどれかが成功すれば(??)
    # これらの順番は優先度を決める: @literaToken は なんでもキャッチする
    i = 0

    # -- code [i..]は「カーソルi以降の全部の文字列」ぐらいの意味
    # -- リテラルを探しながらそのリテラルをトークンストリームに追加し、
    # -- tokenの文字列長だけカーソルを進める
    # 空文字になったら終了
    while @chunk = code[i..]
      # consumed = そのリテラルが使う文字列長
      consumed = \
           # 識別子
           @identifierToken() or
           # コメント
           @commentToken()    or
           # 空白
           @whitespaceToken() or
           # 行
           @lineToken()       or
           # heredoc
           @heredocToken()    or
           # 文字列
           @stringToken()     or
           # 数字
           @numberToken()     or
           # 正規表現
           @regexToken()      or
           # raw js
           @jsToken()         or
           # リテラル(その他)
           @literalToken()

      # Update position
      # 現在の行と列をconsumedだけすすめて更新
      [@chunkLine, @chunkColumn] = @getLineAndColumnFromChunk consumed

      # カーソルを追加
      i += consumed

    # 現在のインデント文を閉じて終わり
    @closeIndentation()

    @error "missing #{tag}" if tag = @ends.pop()
    return @tokens if opts.rewrite is off
    (new Rewriter).rewrite @tokens

  # Preprocess the code to remove leading and trailing whitespace, carriage
  # returns, etc. If we're lexing literate CoffeeScript, strip external Markdown
  # by removing all lines that aren't indented by at least four spaces or a tab.

  # 末尾スペースの除去や重複したreturnの除去などを行う。
  # literate coffeescript モードでは、外部のmarkdownをインデントレベル最低4space か tab によって除去する
  clean: (code) ->
    code = code.slice(1) if code.charCodeAt(0) is BOM
    code = code.replace(/\r/g, '').replace TRAILING_SPACES, ''
    if WHITESPACE.test code
        code = "\n#{code}"
        @chunkLine--
    code = invertLiterate code if @literate
    code

  # Tokenizers
  # ----------

  # Matches identifying literals: variables, keywords, method names, etc.
  # Check to ensure that JavaScript reserved words aren't being used as
  # identifiers. Because CoffeeScript reserves a handful of keywords that are
  # allowed in JavaScript, we're careful not to tag them as keywords when
  # referenced as property names here, so you can still do `jQuery.is()` even
  # though `is` means `===` otherwise.

  # 変数、キーワード、メソッド名、その他の識別子リテラルにマッチする。
  # 識別子として使うことができないJavaScriptの予約語に引っかからないか確認する。
  # CoffeeScriptはJavaScriptの中で便利なキーワードを予約しているので、
  # プロパティとしてここで変数名を参照にするときに、キーワードとしてタグをつけないように気をつける
  # そうすることで、たとえ is が === であっても、jQuery.is() を使うことができる。

  identifierToken: ->
    # 識別子に引っかからなかったら 0
    return 0 unless match = IDENTIFIER.exec @chunk
    [input, id, colon] = match
    # このフォーマットでうまく正規表現からパラメタがうまくとれない…　どんなとき？

    # Preserve length of id for location data
    # location data の配列長を事前予約?
    idLength = id.length

    # 否定演算子でtokenをpopさせたときなどに使用 (用途はまだ不明)
    poppedToken = undefined

    # id が自分自身でかつ tagが'FOR'ステートメントの場合
    # @tag() は引数なしの場合ストリームの先頭を指す
    if id is 'own' and @tag() is 'FOR'
      # [OWN,own] の tokenをつくってownの文字列長(3)を返す
      @token 'OWN', id
      return id.length
    # コロンが存在する、または　直前のtokenが存在し、かつprev.tagが ['.', '?.', '::', '?::']に含まれる場合
    # または spacedではなく、直前のtagが this の場合、強制的に識別子にするフラグを立てる
    forcedIdentifier = colon or
      (prev = last @tokens) and (prev[0] in ['.', '?.', '::', '?::'] or
      not prev.spaced and prev[0] is '@')

    # 識別子
    # -- 次のifステートメントではすぐtagを書き換えるので、意味スコープ的にはもうちょっと下
    tag = 'IDENTIFIER'

    # 強制識別子ではなく、id が jsかcoffeeの予約語に含まれてる場合、
    # -- つまりは文法リテラル
    if not forcedIdentifier and (id in JS_KEYWORDS or id in COFFEE_KEYWORDS)
      # tag は idをアッパケースにしたもの
      # if -> IF,  for -> For
      tag = id.toUpperCase()

      # 現在タグが WHEN かつ 最後の行が次のものに含まれる
      # LINE_BREAK = ['INDENT', 'OUTDENT', 'TERMINATOR']
      # その場合、LEADING_WHEN で 条件文が来ることを予測する
      if tag is 'WHEN' and @tag() in LINE_BREAK
        tag = 'LEADING_WHEN'

      # tagがFOR の場合、@seenFor = yes でfor文を読むモードに入る
      else if tag is 'FOR'
        @seenFor = yes

      # tagがUNLESSの場合、if にする
      # 条件判定は別の箇所でやるのか？
      else if tag is 'UNLESS'
        tag = 'IF'

      # tag が UNARY ['!', '~', 'NEW', 'TYPEOF', 'DELETE', 'DO'] に含まれる
      else if tag in UNARY
        tag = 'UNARY'

      # tagがRELATION識別子['IN', 'OF', 'INSTANCEOF']に含まれる場合
      else if tag in RELATION
        # 今現在forステートメントでありかつ, IN OF のどちらかならば
        # TAGは FORIN , FOROFを返し、forステートメントを解除する
        # -- for i in
        if tag isnt 'INSTANCEOF' and @seenFor
          tag = 'FOR' + tag
          @seenFor = no

        # イテレーションの表現でない場合
        # tag はRELATIONとし,
        # 現在の値が !(否定演算子) の場合、poppedToken に最後の状態を入れて、id は !idとする
        else
          tag = 'RELATION'
          if @value() is '!'
            poppedToken = @tokens.pop()
            id = '!' + id

    # id が JSで使用することを禁じられている場合
    # たぶん将来のための予約後(ES.next)
    if id in JS_FORBIDDEN
      # 強制識別子ならトークンを生成
      # -- ES上で禁止されている用語でも、CoffeeScript上でパース出来れば問題ないというスタンスか
      if forcedIdentifier
        tag = 'IDENTIFIER'
        id  = new String id
        id.reserved = yes
      # CoffeeScriptで使えない予約語は例外
      # - function とか 継承のための __extend とか
      else if id in RESERVED
        @error "reserved word \"#{id}\""

    # 強制識別子でない場合
    unless forcedIdentifier
      # id にエイリアスが登録されている場合、それを使う
      # COFFEE_ALIAS_MAP =
      #   and  : '&&'
      #   or   : '||'
      #   is   : '=='
      #   isnt : '!='
      #   not  : '!'
      #   yes  : 'true'
      #   no   : 'false'
      #   on   : 'true'
      #   off  : 'false'
      id  = COFFEE_ALIAS_MAP[id] if id in COFFEE_ALIASES
      # tagの分類は id実体次第
      tag = switch id
        when '!'                 then 'UNARY'
        when '==', '!='          then 'COMPARE'
        when '&&', '||'          then 'LOGIC'
        when 'true', 'false'     then 'BOOL'
        when 'break', 'continue' then 'STATEMENT'
        else  tag

    # tokenを追加しつつ取得
    tagToken = @token tag, id, 0, idLength
    # 値がpopしていた場合、tagTokenの位置はpoppedTokenのものにあわせる
    # -- 理由がわからない あとで
    if poppedToken
      [tagToken[2].first_line, tagToken[2].first_column] =
        [poppedToken[2].first_line, poppedToken[2].first_column]
    # : がある場合 : tokenをつくる
    if colon
      colonOffset = input.lastIndexOf ':'
      @token ':', ':', colonOffset, colon.length

    # 入力された文字の文字列長を返す
    input.length

  # Matches numbers, including decimals, hex, and exponential notation.
  # Be careful not to interfere with ranges-in-progress.

  # 数字トークン
  # hexとかにも対応
  # range-in-proglressを邪魔しないよう気をつけろ
  numberToken: ->
    return 0 unless match = NUMBER.exec @chunk
    number = match[0]
    # 0X は例外
    if /^0[BOX]/.test number
      @error "radix prefix '#{number}' must be lowercase"
    # 0xを含まない場合例外
    else if /E/.test(number) and not /^0x/.test number
      @error "exponential notation '#{number}' must be indicated with a lowercase 'e'"
    else if /^0\d*[89]/.test number
      @error "decimal literal '#{number}' must not be prefixed with '0'"
    else if /^0\d+/.test number
      @error "octal literal '#{number}' must be prefixed with '0o'"
    # 数字リテラルの構文上の長さ
    lexedLength = number.length
    # 32進数
    if octalLiteral = /^0o([0-7]+)/.exec number
      number = '0x' + (parseInt octalLiteral[1], 8).toString 16
    # 2進数
    if binaryLiteral = /^0b([01]+)/.exec number
      number = '0x' + (parseInt binaryLiteral[1], 2).toString 16
    @token 'NUMBER', number, 0, lexedLength
    lexedLength
  # ====================
  # 疲れたのであとは適宜読む
  # =================

  # Matches strings, including multi-line strings. Ensures that quotation marks
  # are balanced within the string's contents, and within nested interpolations.
  stringToken: ->
    switch @chunk.charAt 0
      when "'"
        return 0 unless match = SIMPLESTR.exec @chunk
        string = match[0]
        @token 'STRING', string.replace(MULTILINER, '\\\n'), 0, string.length
      when '"'
        return 0 unless string = @balancedString @chunk, '"'
        if 0 < string.indexOf '#{', 1
          @interpolateString string[1...-1], strOffset: 1, lexedLength: string.length
        else
          @token 'STRING', @escapeLines string, 0, string.length
      else
        return 0
    if octalEsc = /^(?:\\.|[^\\])*\\(?:0[0-7]|[1-7])/.test string
      @error "octal escape sequences #{string} are not allowed"
    string.length

  # Matches heredocs, adjusting indentation to the correct level, as heredocs
  # preserve whitespace, but ignore indentation to the left.
  heredocToken: ->
    return 0 unless match = HEREDOC.exec @chunk
    heredoc = match[0]
    quote = heredoc.charAt 0
    doc = @sanitizeHeredoc match[2], quote: quote, indent: null
    if quote is '"' and 0 <= doc.indexOf '#{'
      @interpolateString doc, heredoc: yes, strOffset: 3, lexedLength: heredoc.length
    else
      @token 'STRING', @makeString(doc, quote, yes), 0, heredoc.length
    heredoc.length

  # Matches and consumes comments.
  commentToken: ->
    return 0 unless match = @chunk.match COMMENT
    [comment, here] = match
    if here
      @token 'HERECOMMENT',
        (@sanitizeHeredoc here,
          herecomment: true, indent: Array(@indent + 1).join(' ')),
        0, comment.length
    comment.length

  # Matches JavaScript interpolated directly into the source via backticks.
  jsToken: ->
    return 0 unless @chunk.charAt(0) is '`' and match = JSTOKEN.exec @chunk
    @token 'JS', (script = match[0])[1...-1], 0, script.length
    script.length

  # Matches regular expression literals. Lexing regular expressions is difficult
  # to distinguish from division, so we borrow some basic heuristics from
  # JavaScript and Ruby.
  regexToken: ->
    return 0 if @chunk.charAt(0) isnt '/'
    if match = HEREGEX.exec @chunk
      length = @heregexToken match
      return length

    prev = last @tokens
    return 0 if prev and (prev[0] in (if prev.spaced then NOT_REGEX else NOT_SPACED_REGEX))
    return 0 unless match = REGEX.exec @chunk
    [match, regex, flags] = match
    if regex[..1] is '/*' then @error 'regular expressions cannot begin with `*`'
    if regex is '//' then regex = '/(?:)/'
    @token 'REGEX', "#{regex}#{flags}", 0, match.length
    match.length

  # Matches multiline extended regular expressions.
  heregexToken: (match) ->
    [heregex, body, flags] = match
    if 0 > body.indexOf '#{'
      re = body.replace(HEREGEX_OMIT, '').replace(/\//g, '\\/')
      if re.match /^\*/ then @error 'regular expressions cannot begin with `*`'
      @token 'REGEX', "/#{ re or '(?:)' }/#{flags}", 0, heregex.length
      return heregex.length
    @token 'IDENTIFIER', 'RegExp', 0, 0
    @token 'CALL_START', '(', 0, 0
    tokens = []
    for token in @interpolateString(body, regex: yes)
      [tag, value] = token
      if tag is 'TOKENS'
        tokens.push value...
      else if tag is 'NEOSTRING'
        continue unless value = value.replace HEREGEX_OMIT, ''
        # Convert NEOSTRING into STRING
        value = value.replace /\\/g, '\\\\'
        token[0] = 'STRING'
        token[1] = @makeString(value, '"', yes)
        tokens.push token
      else
        @error "Unexpected #{tag}"

      prev = last @tokens
      plusToken = ['+', '+']
      plusToken[2] = prev[2] # Copy location data
      tokens.push plusToken

    # Remove the extra "+"
    tokens.pop()

    unless tokens[0]?[0] is 'STRING'
      @token 'STRING', '""', 0, 0
      @token '+', '+', 0, 0
    @tokens.push tokens...

    if flags
      # Find the flags in the heregex
      flagsOffset = heregex.lastIndexOf flags
      @token ',', ',', flagsOffset, 0
      @token 'STRING', '"' + flags + '"', flagsOffset, flags.length

    @token ')', ')', heregex.length-1, 0
    heregex.length

  # Matches newlines, indents, and outdents, and determines which is which.
  # If we can detect that the current line is continued onto the the next line,
  # then the newline is suppressed:
  #
  #     elements
  #       .each( ... )
  #       .map( ... )
  #
  # Keeps track of the level of indentation, because a single outdent token
  # can close multiple indents, so we need to know how far in we happen to be.
  lineToken: ->
    return 0 unless match = MULTI_DENT.exec @chunk
    indent = match[0]
    @seenFor = no
    size = indent.length - 1 - indent.lastIndexOf '\n'
    noNewlines = @unfinished()
    if size - @indebt is @indent
      if noNewlines then @suppressNewlines() else @newlineToken 0
      return indent.length

    if size > @indent
      if noNewlines
        @indebt = size - @indent
        @suppressNewlines()
        return indent.length
      diff = size - @indent + @outdebt
      @token 'INDENT', diff, indent.length - size, size
      @indents.push diff
      @ends.push 'OUTDENT'
      @outdebt = @indebt = 0
    else
      @indebt = 0
      @outdentToken @indent - size, noNewlines, indent.length
    @indent = size
    indent.length

  # Record an outdent token or multiple tokens, if we happen to be moving back
  # inwards past several recorded indents.

  # もしいくつかの内部で記録されたインデントを遡る時
  # outdent token や その他複数のトークンを記録する
  outdentToken: (moveOut, noNewlines, outdentLength) ->
    while moveOut > 0
      # 現在のインデントブロックの深さ
      len = @indents.length - 1

      # もしindents[len] の実体がない場合、moveOutを0に
      if @indents[len] is undefined
        moveOut = 0
      # 現在のoutdebtがインデントと一致する時, outdebtを0にする
      else if @indents[len] is @outdebt
        moveOut -= @outdebt
        @outdebt = 0
      # 現在のoutdebtがインデントより大きい時, outdebtとmoveOutを減らす
      #     a = [
      #     1
      #     1
      #     1
      #   ]
      # outdebtってこんなやつの前借りindentってこと？
      else if @indents[len] < @outdebt
        @outdebt -= @indents[len]
        moveOut  -= @indents[len]
      else
        # 文字幅はインデント幅とoutdebt量
        dent = @indents.pop() + @outdebt
        moveOut -= dent
        @outdebt = 0
        @pair 'OUTDENT'
        @token 'OUTDENT', dent, 0, outdentLength

    # 文字幅文outdebtを減らす
    @outdebt -= moveOut if dent
    # 末尾セミコロンの除去
    # -- 　末尾セミコロンが挟まってもブロックは解除されない?
    @tokens.pop() while @value() is ';'

    # 現在トークンが終端文字でない、あるいは no;NewLineでないならば、終端トークンを追加
    @token 'TERMINATOR', '\n', outdentLength, 0 unless @tag() is 'TERMINATOR' or noNewlines

    this

  # Matches and consumes non-meaningful whitespace. Tag the previous token
  # as being "spaced", because there are some cases where it makes a difference.
  whitespaceToken: ->
    return 0 unless (match = WHITESPACE.exec @chunk) or
                    (nline = @chunk.charAt(0) is '\n')
    prev = last @tokens
    prev[if match then 'spaced' else 'newLine'] = true if prev
    if match then match[0].length else 0

  # Generate a newline token. Consecutive newlines get merged together.
  newlineToken: (offset) ->
    @tokens.pop() while @value() is ';'
    @token 'TERMINATOR', '\n', offset, 0 unless @tag() is 'TERMINATOR'
    this

  # Use a `\` at a line-ending to suppress the newline.
  # The slash is removed here once its job is done.
  suppressNewlines: ->
    @tokens.pop() if @value() is '\\'
    this

  # We treat all other single characters as a token. E.g.: `( ) , . !`
  # Multi-character operators are also literal tokens, so that Jison can assign
  # the proper order of operations. There are some symbols that we tag specially
  # here. `;` and newlines are both treated as a `TERMINATOR`, we distinguish
  # parentheses that indicate a method call from regular parentheses, and so on.
  literalToken: ->
    if match = OPERATOR.exec @chunk
      [value] = match
      @tagParameters() if CODE.test value
    else
      value = @chunk.charAt 0
    tag  = value
    prev = last @tokens
    if value is '=' and prev
      if not prev[1].reserved and prev[1] in JS_FORBIDDEN
        @error "reserved word \"#{@value()}\" can't be assigned"
      if prev[1] in ['||', '&&']
        prev[0] = 'COMPOUND_ASSIGN'
        prev[1] += '='
        return value.length
    if value is ';'
      @seenFor = no
      tag = 'TERMINATOR'
    else if value in MATH            then tag = 'MATH'
    else if value in COMPARE         then tag = 'COMPARE'
    else if value in COMPOUND_ASSIGN then tag = 'COMPOUND_ASSIGN'
    else if value in UNARY           then tag = 'UNARY'
    else if value in SHIFT           then tag = 'SHIFT'
    else if value in LOGIC or value is '?' and prev?.spaced then tag = 'LOGIC'
    else if prev and not prev.spaced
      if value is '(' and prev[0] in CALLABLE
        prev[0] = 'FUNC_EXIST' if prev[0] is '?'
        tag = 'CALL_START'
      else if value is '[' and prev[0] in INDEXABLE
        tag = 'INDEX_START'
        switch prev[0]
          when '?'  then prev[0] = 'INDEX_SOAK'
    switch value
      when '(', '{', '[' then @ends.push INVERSES[value]
      when ')', '}', ']' then @pair value
    @token tag, value
    value.length

  # Token Manipulators
  # ------------------

  # Sanitize a heredoc or herecomment by
  # erasing all external indentation on the left-hand side.
  sanitizeHeredoc: (doc, options) ->
    {indent, herecomment} = options
    if herecomment
      if HEREDOC_ILLEGAL.test doc
        @error "block comment cannot contain \"*/\", starting"
      return doc if doc.indexOf('\n') < 0
    else
      while match = HEREDOC_INDENT.exec doc
        attempt = match[1]
        indent = attempt if indent is null or 0 < attempt.length < indent.length
    doc = doc.replace /// \n #{indent} ///g, '\n' if indent
    doc = doc.replace /\n# \n/g, '\n\n' if @literate
    doc = doc.replace /^\n/, '' unless herecomment
    doc

  # A source of ambiguity in our grammar used to be parameter lists in function
  # definitions versus argument lists in function calls. Walk backwards, tagging
  # parameters specially in order to make things easier for the parser.
  tagParameters: ->
    return this if @tag() isnt ')'
    stack = []
    {tokens} = this
    i = tokens.length
    tokens[--i][0] = 'PARAM_END'
    while tok = tokens[--i]
      switch tok[0]
        when ')'
          stack.push tok
        when '(', 'CALL_START'
          if stack.length then stack.pop()
          else if tok[0] is '('
            tok[0] = 'PARAM_START'
            return this
          else return this
    this

  # Close up all remaining open blocks at the end of the file.
  closeIndentation: ->
    @outdentToken @indent

  # Matches a balanced group such as a single or double-quoted string. Pass in
  # a series of delimiters, all of which must be nested correctly within the
  # contents of the string. This method allows us to have strings within
  # interpolations within strings, ad infinitum.
  balancedString: (str, end) ->
    continueCount = 0
    stack = [end]
    for i in [1...str.length]
      if continueCount
        --continueCount
        continue
      switch letter = str.charAt i
        when '\\'
          ++continueCount
          continue
        when end
          stack.pop()
          unless stack.length
            return str[0..i]
          end = stack[stack.length - 1]
          continue
      if end is '}' and letter in ['"', "'"]
        stack.push end = letter
      else if end is '}' and letter is '/' and match = (HEREGEX.exec(str[i..]) or REGEX.exec(str[i..]))
        continueCount += match[0].length - 1
      else if end is '}' and letter is '{'
        stack.push end = '}'
      else if end is '"' and prev is '#' and letter is '{'
        stack.push end = '}'
      prev = letter
    @error "missing #{ stack.pop() }, starting"

  # Expand variables and expressions inside double-quoted strings using
  # Ruby-like notation for substitution of arbitrary expressions.
  #
  #     "Hello #{name.capitalize()}."
  #
  # If it encounters an interpolation, this method will recursively create a
  # new Lexer, tokenize the interpolated contents, and merge them into the
  # token stream.
  #
  #  - `str` is the start of the string contents (IE with the " or """ stripped
  #    off.)
  #  - `options.offsetInChunk` is the start of the interpolated string in the
  #    current chunk, including the " or """, etc...  If not provided, this is
  #    assumed to be 0.  `options.lexedLength` is the length of the
  #    interpolated string, including both the start and end quotes.  Both of these
  #    values are ignored if `options.regex` is true.
  #  - `options.strOffset` is the offset of str, relative to the start of the
  #    current chunk.
  interpolateString: (str, options = {}) ->
    {heredoc, regex, offsetInChunk, strOffset, lexedLength} = options
    offsetInChunk = offsetInChunk || 0
    strOffset = strOffset || 0
    lexedLength = lexedLength || str.length

    # Clip leading \n from heredoc
    if heredoc and str.length > 0 and str[0] == '\n'
      str = str[1...]
      strOffset++

    # Parse the string.
    tokens = []
    pi = 0
    i  = -1
    while letter = str.charAt i += 1
      if letter is '\\'
        i += 1
        continue
      unless letter is '#' and str.charAt(i+1) is '{' and
             (expr = @balancedString str[i + 1..], '}')
        continue
      # NEOSTRING is a fake token.  This will be converted to a string below.
      tokens.push @makeToken('NEOSTRING', str[pi...i], strOffset + pi) if pi < i
      inner = expr[1...-1]
      if inner.length
        [line, column] = @getLineAndColumnFromChunk(strOffset + i + 1)
        nested = new Lexer().tokenize inner, line: line, column: column, rewrite: off
        popped = nested.pop()
        popped = nested.shift() if nested[0]?[0] is 'TERMINATOR'
        if len = nested.length
          if len > 1
            nested.unshift @makeToken '(', '(', strOffset + i + 1, 0
            nested.push    @makeToken ')', ')', strOffset + i + 1 + inner.length, 0
          # Push a fake 'TOKENS' token, which will get turned into real tokens below.
          tokens.push ['TOKENS', nested]
      i += expr.length
      pi = i + 1
    tokens.push @makeToken('NEOSTRING', str[pi..], strOffset + pi) if i > pi < str.length

    # If regex, then return now and let the regex code deal with all these fake tokens
    return tokens if regex

    # If we didn't find any tokens, then just return an empty string.
    return @token 'STRING', '""', offsetInChunk, lexedLength unless tokens.length

    # If the first token is not a string, add a fake empty string to the beginning.
    tokens.unshift @makeToken('NEOSTRING', '', offsetInChunk) unless tokens[0][0] is 'NEOSTRING'

    @token '(', '(', offsetInChunk, 0 if interpolated = tokens.length > 1
    # Push all the tokens
    for token, i in tokens
      [tag, value] = token
      if i
        # Create a 0-length "+" token.
        plusToken = @token '+', '+' if i
        locationToken = if tag == 'TOKENS' then value[0] else token
        plusToken[2] =
          first_line: locationToken[2].first_line
          first_column: locationToken[2].first_column
          last_line: locationToken[2].first_line
          last_column: locationToken[2].first_column
      if tag is 'TOKENS'
        # Push all the tokens in the fake 'TOKENS' token.  These already have
        # sane location data.
        @tokens.push value...
      else if tag is 'NEOSTRING'
        # Convert NEOSTRING into STRING
        token[0] = 'STRING'
        token[1] = @makeString value, '"', heredoc
        @tokens.push token
      else
        @error "Unexpected #{tag}"
    if interpolated
      rparen = @makeToken ')', ')', offsetInChunk + lexedLength, 0
      rparen.stringEnd = true
      @tokens.push rparen
    tokens

  # Pairs up a closing token, ensuring that all listed pairs of tokens are
  # correctly balanced throughout the course of the token stream.
  pair: (tag) ->
    unless tag is wanted = last @ends
      @error "unmatched #{tag}" unless 'OUTDENT' is wanted
      # Auto-close INDENT to support syntax like this:
      #
      #     el.click((event) ->
      #       el.hide())
      #
      @indent -= size = last @indents
      @outdentToken size, true
      return @pair tag
    @ends.pop()

  # Helpers
  # -------

  # Returns the line and column number from an offset into the current chunk.
  #
  # `offset` is a number of characters into @chunk.

  # ヘルパ
  # 現在のチャンクのoffsetから行と列を返す
  # offset は チャンクに対する文字列の数である
  getLineAndColumnFromChunk: (offset) ->
    if offset is 0
      return [@chunkLine, @chunkColumn]

    if offset >= @chunk.length
      string = @chunk
    else
      string = @chunk[..offset-1]

    lineCount = count string, '\n'

    column = @chunkColumn
    if lineCount > 0
      lines = string.split '\n'
      column = (last lines).length
    else
      column += string.length

    [@chunkLine + lineCount, column]

  # Same as "token", exception this just returns the token without adding it
  # to the results.

  # token と同様だが、これは単に tokenを追加することなくtokenを生成するだけ
  makeToken: (tag, value, offsetInChunk = 0, length = value.length) ->
    locationData = {}
    # 開始行、列を取得
    [locationData.first_line, locationData.first_column] =
      @getLineAndColumnFromChunk offsetInChunk

    # Use length - 1 for the final offset - we're supplying the last_line and the last_column,
    # so if last_column == first_column, then we're looking at a character of length 1.

    # 最後のオフセットのために length - 1 を使う
    # 私たちは最後の行と列を提供している。
    # なので 最終行と開始行が一緒なら、私たちは length 1 の文字列を探す
    lastCharacter = Math.max 0, length - 1
    [locationData.last_line, locationData.last_column] =
      @getLineAndColumnFromChunk offsetInChunk + (lastCharacter)

    token = [tag, value, locationData]

    token

  # Add a token to the results.
  # `offset` is the offset into the current @chunk where the token starts.
  # `length` is the length of the token in the @chunk, after the offset.  If
  # not specified, the length of `value` will be used.
  #
  # Returns the new token.

  # トークンを探してストリームに追加し、そのトークンを返す
  token: (tag, value, offsetInChunk, length) ->
    token = @makeToken tag, value, offsetInChunk, length
    @tokens.push token
    token

  # Peek at a tag in the current token stream.
  # 現在のトークンストリームのタグを覗く
  # 説明が不適切のように思える。第二引数がある場合はset
  tag: (index, tag) ->
    # tok は 何も指定しなければ先頭のtokenを指す
    # tagが指定されていれば tagを更新する。そうでなければそのままtagを取得
    # 要はjQuery#text みたいな get系とset系の同居
    # token : [tag, value, locationData]
    (tok = last @tokens, index) and (if tag then (tok[0] = tag) else tok[0])

  # Peek at a value in the current token stream.
  # 上記のtag関数のtoken第二匹数のvalue版
  value: (index, val) ->
    (tok = last @tokens, index) and if val then tok[1] = val else tok[1]

  # Are we in the midst of an unfinished expression?
  unfinished: ->
    LINE_CONTINUER.test(@chunk) or
    @tag() in ['\\', '.', '?.', '?::', 'UNARY', 'MATH', '+', '-', 'SHIFT', 'RELATION'
               'COMPARE', 'LOGIC', 'THROW', 'EXTENDS']

  # Converts newlines for string literals.
  escapeLines: (str, heredoc) ->
    str.replace MULTILINER, if heredoc then '\\n' else ''

  # Constructs a string token by escaping quotes and newlines.
  makeString: (body, quote, heredoc) ->
    return quote + quote unless body
    body = body.replace /\\([\s\S])/g, (match, contents) ->
      if contents in ['\n', quote] then contents else match
    body = body.replace /// #{quote} ///g, '\\$&'
    quote + @escapeLines(body, heredoc) + quote

  # Throws a syntax error on the current `@line`.
  error: (message) ->
    # TODO: Are there some cases we could improve the error line number by
    # passing the offset in the chunk where the error happened?
    throw SyntaxError "#{message} on line #{ @chunkLine + 1 }"

# Constants
# ---------

# Keywords that CoffeeScript shares in common with JavaScript.
JS_KEYWORDS = [
  'true', 'false', 'null', 'this'
  'new', 'delete', 'typeof', 'in', 'instanceof'
  'return', 'throw', 'break', 'continue', 'debugger'
  'if', 'else', 'switch', 'for', 'while', 'do', 'try', 'catch', 'finally'
  'class', 'extends', 'super'
]

# CoffeeScript-only keywords.
COFFEE_KEYWORDS = ['undefined', 'then', 'unless', 'until', 'loop', 'of', 'by', 'when']

COFFEE_ALIAS_MAP =
  and  : '&&'
  or   : '||'
  is   : '=='
  isnt : '!='
  not  : '!'
  yes  : 'true'
  no   : 'false'
  on   : 'true'
  off  : 'false'

COFFEE_ALIASES  = (key for key of COFFEE_ALIAS_MAP)
COFFEE_KEYWORDS = COFFEE_KEYWORDS.concat COFFEE_ALIASES

# The list of keywords that are reserved by JavaScript, but not used, or are
# used by CoffeeScript internally. We throw an error when these are encountered,
# to avoid having a JavaScript error at runtime.

# JavaScriptで予約されていて、CoffeeScriptで内部的に使われているもの
# JavaScriptのランタイムエラーを避けるためにこれらのキーワードをみつけると例外を投げる
RESERVED = [
  'case', 'default', 'function', 'var', 'void', 'with', 'const', 'let', 'enum'
  'export', 'import', 'native', '__hasProp', '__extends', '__slice', '__bind'
  '__indexOf', 'implements', 'interface', 'package', 'private', 'protected'
  'public', 'static', 'yield'
]

STRICT_PROSCRIBED = ['arguments', 'eval']

# The superset of both JavaScript keywords and reserved words, none of which may
# be used as identifiers or properties.
JS_FORBIDDEN = JS_KEYWORDS.concat(RESERVED).concat(STRICT_PROSCRIBED)

exports.RESERVED = RESERVED.concat(JS_KEYWORDS).concat(COFFEE_KEYWORDS).concat(STRICT_PROSCRIBED)
exports.STRICT_PROSCRIBED = STRICT_PROSCRIBED

# The character code of the nasty Microsoft madness otherwise known as the BOM.
BOM = 65279

# Token matching regexes.
# トークンにマッチする正規表現
IDENTIFIER = /// ^
  ( [$A-Za-z_\x7f-\uffff][$\w\x7f-\uffff]* )
  ( [^\n\S]* : (?!:) )?  # Is this a property name?
///

NUMBER     = ///
  ^ 0b[01]+    |              # binary
  ^ 0o[0-7]+   |              # octal
  ^ 0x[\da-f]+ |              # hex
  ^ \d*\.?\d+ (?:e[+-]?\d+)?  # decimal
///i

HEREDOC    = /// ^ ("""|''') ([\s\S]*?) (?:\n[^\n\S]*)? \1 ///

OPERATOR   = /// ^ (
  ?: [-=]>             # function
   | [-+*/%<>&|^!?=]=  # compound assign / compare
   | >>>=?             # zero-fill right shift
   | ([-+:])\1         # doubles
   | ([&|<>])\2=?      # logic / shift
   | \?(\.|::)         # soak access
   | \.{2,3}           # range or splat
) ///

WHITESPACE = /^[^\n\S]+/

COMMENT    = /^###([^#][\s\S]*?)(?:###[^\n\S]*|(?:###)$)|^(?:\s*#(?!##[^#]).*)+/

CODE       = /^[-=]>/

MULTI_DENT = /^(?:\n[^\n\S]*)+/

SIMPLESTR  = /^'[^\\']*(?:\\.[^\\']*)*'/

JSTOKEN    = /^`[^\\`]*(?:\\.[^\\`]*)*`/

# Regex-matching-regexes.
REGEX = /// ^
  (/ (?! [\s=] )   # disallow leading whitespace or equals signs
  [^ [ / \n \\ ]*  # every other thing
  (?:
    (?: \\[\s\S]   # anything escaped
      | \[         # character class
           [^ \] \n \\ ]*
           (?: \\[\s\S] [^ \] \n \\ ]* )*
         ]
    ) [^ [ / \n \\ ]*
  )*
  /) ([imgy]{0,4}) (?!\w)
///

HEREGEX      = /// ^ /{3} ([\s\S]+?) /{3} ([imgy]{0,4}) (?!\w) ///

HEREGEX_OMIT = /\s+(?:#.*)?/g

# Token cleaning regexes.
MULTILINER      = /\n/g

HEREDOC_INDENT  = /\n+([^\n\S]*)/g

HEREDOC_ILLEGAL = /\*\//

LINE_CONTINUER  = /// ^ \s* (?: , | \??\.(?![.\d]) | :: ) ///

TRAILING_SPACES = /\s+$/

# Compound assignment tokens.
COMPOUND_ASSIGN = [
  '-=', '+=', '/=', '*=', '%=', '||=', '&&=', '?=', '<<=', '>>=', '>>>=', '&=', '^=', '|='
]

# Unary tokens.
UNARY   = ['!', '~', 'NEW', 'TYPEOF', 'DELETE', 'DO']

# Logical tokens.
LOGIC   = ['&&', '||', '&', '|', '^']

# Bit-shifting tokens.
SHIFT   = ['<<', '>>', '>>>']

# Comparison tokens.
COMPARE = ['==', '!=', '<', '>', '<=', '>=']

# Mathematical tokens.
MATH    = ['*', '/', '%']

# Relational tokens that are negatable with `not` prefix.
RELATION = ['IN', 'OF', 'INSTANCEOF']

# Boolean tokens.
BOOL = ['TRUE', 'FALSE']

# Tokens which a regular expression will never immediately follow, but which
# a division operator might.
#
# See: http://www.mozilla.org/js/language/js20-2002-04/rationale/syntax.html#regular-expressions
#
# Our list is shorter, due to sans-parentheses method calls.
NOT_REGEX = ['NUMBER', 'REGEX', 'BOOL', 'NULL', 'UNDEFINED', '++', '--', ']']

# If the previous token is not spaced, there are more preceding tokens that
# force a division parse:
NOT_SPACED_REGEX = NOT_REGEX.concat ')', '}', 'THIS', 'IDENTIFIER', 'STRING'

# Tokens which could legitimately be invoked or indexed. An opening
# parentheses or bracket following these tokens will be recorded as the start
# of a function invocation or indexing operation.
CALLABLE  = ['IDENTIFIER', 'STRING', 'REGEX', ')', ']', '}', '?', '::', '@', 'THIS', 'SUPER']
INDEXABLE = CALLABLE.concat 'NUMBER', 'BOOL', 'NULL', 'UNDEFINED'

# Tokens that, when immediately preceding a `WHEN`, indicate that the `WHEN`
# occurs at the start of a line. We disambiguate these from trailing whens to
# avoid an ambiguity in the grammar.
LINE_BREAK = ['INDENT', 'OUTDENT', 'TERMINATOR']
