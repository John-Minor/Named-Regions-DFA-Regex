package main

import "core:fmt"
import "core:time"
import "core:runtime"
import "core:unicode"
import "core:mem"

Stack :: struct(T :typeid)
{
    head :int,
    elements :[]T,
}

// if these stack functions are inlined the program will always crash during the set up phase for lexing when using anything but -opt:0
make_stack :: inline proc($T :typeid, len :int, allocator := context.allocator) -> (stack :Stack(T))
{
    using stack;
    head = 0;
    elements = make([]T, len, allocator);
    return;
}

make_temp_stack :: inline proc($T :typeid, len :int, allocator := context.temp_allocator) -> Stack(T)
{
    return make_stack(T, len, allocator);
}

delete_stack :: inline proc(stack :Stack($T))
{
    delete(stack.elements);
}

push :: inline proc(using stack :^Stack($T), element :T)
{
    elements[head] = element;
    head += 1;
}

pop :: inline proc(using stack :^Stack($T)) -> T
{
    head -= 1;
    return elements[head];
}

peek :: inline proc(using stack :^Stack($T)) -> T
{
    return elements[head - 1];
}

peek_pointer :: inline proc(using stack :^Stack($T)) -> ^T
{
    return &elements[head - 1];
}

push_unsafe :: inline proc(using stack :^Stack($T), element :T)
{
    #no_bounds_check elements[head] = element;
    head += 1;
}

pop_unsafe :: inline proc(using stack :^Stack($T)) -> T
{
    head -= 1;
    return #no_bounds_check elements[head];
}

peek_unsafe :: inline proc(using stack :^Stack($T)) -> T
{
    return #no_bounds_check elements[head - 1];
}

peek_pointer_unsafe :: inline proc(using stack :^Stack($T)) -> ^T
{
    return #no_bounds_check &elements[head - 1];
}

Character_Type :: enum
{
    NON_MATCHING,
    EXACT,
    RANGE,
    NUM,
    NOT_NUM,
    LOWER,
    NOT_LOWER,
    UPPER,
    NOT_UPPER,
    WORD,
    NOT_WORD,
    WHITESPACE,
    NOT_WHITESPACE,
    VERTICAL_WHITESPACE,
    NOT_VERTICAL_WHITESPACE,
    HORIZONTAL_WHITESPACE,
    NOT_HORIZONTAL_WHITESPACE,
}

Character :: struct
{
    min_rune :rune,
    max_rune :rune,
    type :Character_Type,
}

Character_Class :: struct
{
    characters :[]Character,
    negated :bool,
}

Character_Value :: union
{
    Character,
    Character_Class,
}

Token :: struct
{
    character_value :Character_Value,
    index :int,
    region_name :u128,
}

Operator :: enum
{
    ALTERN = 0,
    CONCAT = 1,
    KLEENE = 2,
    EXIST = 3,
    REPEAT = 4,
}

Precedence :: enum
{
    INVALID_PRECEDENCE = -5,
    OPERAND = -1,
    OPAREN = 0,
    ALTERN = 1,
    CONCAT = 2,
    UNARY = 3,
    CLOPAREN = 4,
}

Node :: struct
{
    token :^Token,
    operation :Operator,
    precedence :Precedence,

    nullable :bool,

    first_pos :[]^Node,
    last_pos :[]^Node,
    follow_pos :[]^Node,

    position :int,
}

CONCAT_NODE :: Node{operation = .CONCAT, precedence = .CONCAT};

Transition :: struct
{
    character_value :Character_Value,
    jump :int,
    region_name :u128,
}

Table_Entry :: struct
{
    transitions :[]Transition,
}

to_region32_slice :: proc(text :[]u8) -> (out :u128)
{
    for character, index in text
    {
        to_bits :u128 = cast(u128)character & 0b000_11111;
        out |= to_bits << cast(u128)(5 * index);
    }
    return;
}

to_region32_string :: proc(text :string) -> (out :u128)
{
    for character, index in text
    {
        to_bits :u128 = cast(u128)character & 0b000_11111;
        out |= to_bits << cast(u128)(5 * index);
    }
    return;
}

to_region32 :: proc{to_region32_slice, to_region32_string};

from_region32 :: proc(value :u128) -> []rune
{
    stack := make_temp_stack(rune, 25);
    for i := 0; i < 26; i += 1
    {
        character := cast(u8)(0b011_00000 | (0b000_11111 & (value >> cast(u128)(5 * i))));
        if character == 0b011_11111 do character = 0b010_11111;
        if character == 0b011_00000 do break;
        push_unsafe(&stack, cast(rune)character);
    }
    return #no_bounds_check stack.elements[0 : stack.head];
}

compile_regex :: proc(regex :string) -> (table :[]Table_Entry, error :string = "", ok := true)
{
    regex_length := len(regex) + 4; // the 4 is because of the 4 characters in: "s(" + regex + ")#"
    if regex_length % 2 != 0 do regex_length += 1; // for some reason the program crashes during lexing if this value is odd and you use anything but -opt:0

    if DEBUG do fmt.println("Regex length:", regex_length, "\n");

    token_stack := make_temp_stack(Token, regex_length);

    { // lexing
        if DEBUG do fmt.println("Lexing started!");

        // always crashes here on -opt:1
        // concat "s(" to the beginning of the regex where 's' has the region name "start"
        push_unsafe(&token_stack, Token{Character{'S', 0, .EXACT}, token_stack.head, to_region32("start")});
        push_unsafe(&token_stack, Token{Character{'(', 0, .NON_MATCHING}, token_stack.head, 0});

        Lex_State :: enum
        {
            NORMAL,
            NAMING,
            ESCAPE,
            CLASS_START,
            CLASS,
            CLASS_RANGE,
            CLASS_RANGE_ESCAPE,
            CLASS_ESCAPE,
        };
        state := Lex_State.NORMAL;

        region_accumulator_stack := make_temp_stack(u8, 25);
        region_names_stack := make_temp_stack(u128, regex_length/2);
        // crashes here on -opt:2 and -opt:3 if the regex_length variable is an odd value
        push_unsafe(&region_names_stack, 0);

        class_stack := make_temp_stack(Character, regex_length);
        negated := false;

        fences := 0;

        for current_rune in regex
        {
            switch state
            {
                case .NORMAL:
                    switch
                    {
                        case current_rune == '{':
                            state = .NAMING;
                            region_accumulator_stack.head = 0;
                        
                        case current_rune == '}':
                            if region_names_stack.head == 1 do return nil, `region name close '}' without region name start '{'`, false;
                            pop_unsafe(&region_names_stack);

                        case current_rune == '\\':
                            state = .ESCAPE;

                        case current_rune == '[':
                            state = .CLASS_START;
                            class_stack.head = 0;
                            negated = false;

                        case current_rune == ']':
                            return nil, `character class close ']' without character class start '['`, false;

                        case current_rune == '('
                        || current_rune == ')'
                        || current_rune == '|'
                        || current_rune == '*'
                        || current_rune == '?'
                        || current_rune == '+':
                            // checking for balanced expression
                            if current_rune == '(' do fences += 1;
                            if current_rune == ')' do fences -= 1;
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .NON_MATCHING}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case current_rune == '.':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .NOT_VERTICAL_WHITESPACE}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case:
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .EXACT}, token_stack.head, peek_unsafe(&region_names_stack)});
                    }

                case .NAMING:
                    switch current_rune
                    {
                        case ':':
                            state = .NORMAL;
                            push_unsafe(&region_names_stack, to_region32(#no_bounds_check region_accumulator_stack.elements[0 : region_accumulator_stack.head]));

                        case:
                            push_unsafe(&region_accumulator_stack, cast(u8)current_rune);
                    }

                case .ESCAPE:
                    state = .NORMAL;
                    switch current_rune
                    {
                        case 'd':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .NUM}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'D':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .NOT_NUM}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'l':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .LOWER}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'L':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .NOT_LOWER}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'u':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .UPPER}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'U':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .NOT_UPPER}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'w':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .WORD}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'W':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .NOT_WORD}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 's':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .WHITESPACE}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'S':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .NOT_WHITESPACE}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'v':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .VERTICAL_WHITESPACE}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'V':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .NOT_VERTICAL_WHITESPACE}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'h':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .HORIZONTAL_WHITESPACE}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'H':
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .NOT_HORIZONTAL_WHITESPACE}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'a': // bell
                            push_unsafe(&token_stack, Token{Character{'\a', 0, .EXACT}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'b': // backspace
                            push_unsafe(&token_stack, Token{Character{'\b', 0, .EXACT}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 't': // tab
                            push_unsafe(&token_stack, Token{Character{'\t', 0, .EXACT}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'r': // carriage return
                            push_unsafe(&token_stack, Token{Character{'\r', 0, .EXACT}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'f': // form feed
                            push_unsafe(&token_stack, Token{Character{'\f', 0, .EXACT}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'n': // new line
                            push_unsafe(&token_stack, Token{Character{'\n', 0, .EXACT}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case 'e': // escape
                            push_unsafe(&token_stack, Token{Character{'\e', 0, .EXACT}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case:
                            push_unsafe(&token_stack, Token{Character{current_rune, 0, .EXACT}, token_stack.head, peek_unsafe(&region_names_stack)});
                    }

                case .CLASS_START:
                    switch current_rune
                    {
                        case '^':
                            state = .CLASS;
                            negated = true;

                        case '-':
                            return nil, `range '-' in character class without range min`, false;

                        case '\\':
                            state = .CLASS_ESCAPE;

                        case '.':
                            push_unsafe(&class_stack, Character{current_rune, 0, .NOT_VERTICAL_WHITESPACE});

                        case '[':
                            return nil, `unescaped character class start '[' within character class`, false;

                        case ']':
                            state = .NORMAL;
                            temp_slice := make([]Character, class_stack.head, context.temp_allocator);
                            runtime.copy_slice(temp_slice, #no_bounds_check class_stack.elements[0 : class_stack.head]);
                            push_unsafe(&token_stack, Token{Character_Class{temp_slice, negated}, token_stack.head, peek_unsafe(&region_names_stack)});

                        case:
                            state = .CLASS;
                            push_unsafe(&class_stack, Character{current_rune, 0, .EXACT});
                    }

                case .CLASS:
                    switch current_rune
                    {
                        case '-':
                            if class_stack.head == 0 do return nil, `range '-' in character class without range min`, false;
                            state = .CLASS_RANGE;

                        case '\\':
                            state = .CLASS_ESCAPE;

                        case '.':
                            push_unsafe(&class_stack, Character{current_rune, 0, .NOT_VERTICAL_WHITESPACE});

                        case '[':
                            return nil, `unescaped character class start '[' within character class`, false;

                        case ']':
                            state = .NORMAL;
                            temp_slice := make([]Character, class_stack.head, context.temp_allocator);
                            runtime.copy_slice(temp_slice, #no_bounds_check class_stack.elements[0 : class_stack.head]);
                            push_unsafe(&token_stack, Token{Character_Class{temp_slice, negated}, token_stack.head, peek_unsafe(&region_names_stack)});


                        case:
                            push_unsafe(&class_stack, Character{current_rune, 0, .EXACT});
                    }

                case .CLASS_RANGE:
                    character := #no_bounds_check &class_stack.elements[class_stack.head - 1];
                    if character.type != .EXACT do return nil, `range '-' in character class with shorthand range min`, false;
                    if current_rune == '.' do return nil, `range '-' in character class with shorthand range max`, false;
                    switch current_rune
                    {
                        case '\\':
                            state = .CLASS_RANGE_ESCAPE;

                        case:
                            state = .CLASS;
                            character.max_rune = current_rune;
                            character.type = .RANGE;
                    }

                case .CLASS_RANGE_ESCAPE:
                    state = .CLASS;
                    
                    escaped_rune := current_rune;
                    switch
                    {
                        case escaped_rune == 'd'
                        || escaped_rune == 'D'
                        || escaped_rune == 'l'
                        || escaped_rune == 'L'
                        || escaped_rune == 'u'
                        || escaped_rune == 'U'
                        || escaped_rune == 'w'
                        || escaped_rune == 'W'
                        || escaped_rune == 's'
                        || escaped_rune == 'S'
                        || escaped_rune == 'v'
                        || escaped_rune == 'V'
                        || escaped_rune == 'h'
                        || escaped_rune == 'H':
                            return nil, `range '-' in character class with shorthand range max`, false;

                        case escaped_rune == 'a':
                            escaped_rune = '\a';

                        case escaped_rune == 'b':
                            escaped_rune = '\b';

                        case escaped_rune == 't':
                            escaped_rune = '\t';

                        case escaped_rune == 'r':
                            escaped_rune = '\r';

                        case escaped_rune == 'f':
                            escaped_rune = '\f';

                        case escaped_rune == 'n':
                            escaped_rune = '\n';

                        case escaped_rune == 'e':
                            escaped_rune = '\e';
                    }

                    character := #no_bounds_check &class_stack.elements[class_stack.head - 1];
                    character.max_rune = escaped_rune;
                    character.type = .RANGE;

                case .CLASS_ESCAPE:
                    state = .CLASS;
                    switch current_rune
                    {
                        case 'd':
                            push_unsafe(&class_stack, Character{current_rune, 0, .NUM});

                        case 'D':
                            push_unsafe(&class_stack, Character{current_rune, 0, .NOT_NUM});

                        case 'l':
                            push_unsafe(&class_stack, Character{current_rune, 0, .LOWER});

                        case 'L':
                            push_unsafe(&class_stack, Character{current_rune, 0, .NOT_LOWER});

                        case 'u':
                            push_unsafe(&class_stack, Character{current_rune, 0, .UPPER});

                        case 'U':
                            push_unsafe(&class_stack, Character{current_rune, 0, .NOT_UPPER});

                        case 'w':
                            push_unsafe(&class_stack, Character{current_rune, 0, .WORD});

                        case 'W':
                            push_unsafe(&class_stack, Character{current_rune, 0, .NOT_WORD});

                        case 's':
                            push_unsafe(&class_stack, Character{current_rune, 0, .WHITESPACE});

                        case 'S':
                            push_unsafe(&class_stack, Character{current_rune, 0, .NOT_WHITESPACE});

                        case 'v':
                            push_unsafe(&class_stack, Character{current_rune, 0, .VERTICAL_WHITESPACE});

                        case 'V':
                            push_unsafe(&class_stack, Character{current_rune, 0, .NOT_VERTICAL_WHITESPACE});

                        case 'h':
                            push_unsafe(&class_stack, Character{current_rune, 0, .HORIZONTAL_WHITESPACE});

                        case 'H':
                            push_unsafe(&class_stack, Character{current_rune, 0, .NOT_HORIZONTAL_WHITESPACE});

                        case 'a': // bell
                            push_unsafe(&class_stack, Character{'\a', 0, .EXACT});

                        case 'b': // backspace
                            push_unsafe(&class_stack, Character{'\b', 0, .EXACT});

                        case 't': // tab
                            push_unsafe(&class_stack, Character{'\t', 0, .EXACT});

                        case 'r': // carriage return
                            push_unsafe(&class_stack, Character{'\r', 0, .EXACT});

                        case 'f': // form feed
                            push_unsafe(&class_stack, Character{'\f', 0, .EXACT});

                        case 'n': // new line
                            push_unsafe(&class_stack, Character{'\n', 0, .EXACT});

                        case 'e': // escape
                            push_unsafe(&class_stack, Character{'\e', 0, .EXACT});

                        case:
                            push_unsafe(&class_stack, Character{current_rune, 0, .EXACT});
                    }
            }
        }

        if state != .NORMAL
        {
            #partial switch state
            {
                case .NAMING:
                    error = `region name start '{' without defined region name, e.g. "some_text:"`;

                case .ESCAPE:
                    error = `escape character start '\' without following character`;

                case .CLASS_START:
                    error = `character class start '[' without closing ']'`;

                case .CLASS:
                    error = `character class start '[' without closing ']'`;

                case .CLASS_RANGE:
                    error = `range '-' in character class without range max`;

                case .CLASS_RANGE_ESCAPE:
                    error = `escape character start '\' without following character in range in character class`;

                case .CLASS_ESCAPE:
                    error = `escape character start '\' without following character in character class`;
            }
            return nil, error, false;
        }

        if fences > 0 do return nil, `imbalanced expression, open parens '(' without matching ')'`, false;
        if fences < 0 do return nil, `imbalanced expression, close parens ')' without matching '('`, false;

        // concat ")#" to the end of the regex where '#' has the region name "accept"
        push_unsafe(&token_stack, Token{Character{')', 0, .NON_MATCHING}, token_stack.head, 0});
        push_unsafe(&token_stack, Token{Character{'#', 0, .EXACT}, token_stack.head, to_region32("accept")});

        if DEBUG do fmt.println("Lexing finished!");
    }

    regex_length = token_stack.head;
    tokens := #no_bounds_check token_stack.elements[0 : regex_length];

    // double the length to account for the implicit concat(.) operator
    max_nodes := regex_length * 2;
    max_operands := regex_length;

    nodes := make_temp_stack(Node, max_nodes);

    rpn := make_temp_stack(^Node, max_nodes);

    { // parsing
        if DEBUG do fmt.println("Parsing started!");

        ops := make_temp_stack(^Node, regex_length);

        shunting_yard :: proc(using current_node :^Node, rpn :^Stack(^Node), ops :^Stack(^Node))
        {
            switch
            {
                case precedence == .OPERAND:
                    push_unsafe(rpn, current_node);

                case precedence == .OPAREN:
                    push_unsafe(ops, current_node);

                case precedence == .ALTERN
                || precedence == .CONCAT
                || precedence == .UNARY:
                    for
                    {
                        if ops.head == 0 || precedence > peek_unsafe(ops).precedence
                        {
                            push_unsafe(ops, current_node);
                            break;
                        }
                        else
                        {
                            push_unsafe(rpn, pop_unsafe(ops));
                        }
                    }

                case precedence == .CLOPAREN:
                    for
                    {
                        if peek_unsafe(ops).precedence != .OPAREN
                        {
                            push_unsafe(rpn, pop_unsafe(ops));
                        }
                        else
                        {
                            pop_unsafe(ops);
                            break;
                        }
                    }
            }
        }

        using current_node :Node;
        precedence = .INVALID_PRECEDENCE;

        for i := 0; i < regex_length; i += 1
        {
            current_token := #no_bounds_check &tokens[i];

            // compute from last precedence value if a concat should be inserted
            l_concatable := precedence == .OPERAND || precedence == .UNARY || precedence == .CLOPAREN;
            r_concatable :bool;
            
            switch character_value in current_token.character_value
            {
                case Character:
                    switch character_value.min_rune
                    {
                        case '(':
                            precedence = .OPAREN;
                            r_concatable = true;

                        case '|':
                            operation = .ALTERN;
                            precedence = .ALTERN;

                        case '*':
                            operation = .KLEENE;
                            precedence = .UNARY;

                        case '?':
                            operation = .EXIST;
                            precedence = .UNARY;

                        case '+':
                            operation = .REPEAT;
                            precedence = .UNARY;

                        case ')':
                            precedence = .CLOPAREN;

                        case:
                            token = current_token;
                            precedence = .OPERAND;
                            r_concatable = true;
                    }

                case Character_Class:
                    token = current_token;
                    precedence = .OPERAND;
                    r_concatable = true;
            }

            // should a concat be inserted?
            if l_concatable && r_concatable
            {
                push_unsafe(&nodes, CONCAT_NODE);
                shunting_yard(peek_pointer_unsafe(&nodes), &rpn, &ops);
            }

            push_unsafe(&nodes, current_node);
            shunting_yard(peek_pointer_unsafe(&nodes), &rpn, &ops);
        }

        for ops.head != 0
        {
            push_unsafe(&rpn, pop_unsafe(&ops));
        }

        if DEBUG do fmt.println("Parsing finished!");
    }

    operands := make_temp_stack(^Node, max_operands);

    { // symbolic evaluation
        if DEBUG do fmt.println("Symbolic evaluation started!");

        eval := make_temp_stack(^Node, max_nodes);

        compute_follow_pos :: proc(first_pos :[]^Node, leaves :[]^Node)
        {
            length := len(leaves);
            for i := 0; i < length; i += 1
            {
                leaf := #no_bounds_check leaves[i];

                leaf.follow_pos = marry_slices(first_pos, leaf.follow_pos);
            }
        }

        marry_slices :: proc(left :[]$T, right :[]T) -> (out :[]T)
        {
            lenl, lenr := len(left), len(right);
            lenlr := lenl + lenr;
            out = make([]T, lenlr, context.temp_allocator);

            outl := #no_bounds_check out[0 : lenl];
            runtime.copy_slice(out, left);

            outr := #no_bounds_check out[lenl : lenlr];
            runtime.copy_slice(outr, right);

            return;
        }

        for i := 0; i < rpn.head; i += 1
        {
            using current_node := #no_bounds_check rpn.elements[i];

            #partial switch precedence
            {
                case .OPERAND:
                    nullable = false;

                    first_pos = make([]^Node, 1, context.temp_allocator);
                    #no_bounds_check first_pos[0] = current_node;

                    last_pos = make([]^Node, 1, context.temp_allocator);
                    #no_bounds_check last_pos[0] = current_node;

                    position = operands.head;

                    push_unsafe(&operands, current_node);
                    push_unsafe(&eval, current_node);

                case .UNARY:
                    if eval.head == 0 do return nil, `imbalanced expression, insufficient operands available for all operators`, false;
                    middle_node := pop_unsafe(&eval);

                    first_pos = middle_node.first_pos;
                    last_pos = middle_node.last_pos;

                    switch
                    {
                        case operation == .KLEENE:
                            nullable = true;

                            compute_follow_pos(middle_node.first_pos, middle_node.last_pos);

                        case operation == .EXIST:
                            nullable = true;

                        case operation == .REPEAT:
                            nullable = middle_node.nullable;

                            compute_follow_pos(middle_node.first_pos, middle_node.last_pos);
                    }

                    push_unsafe(&eval, current_node);

                case .ALTERN:
                    if eval.head == 1 do return nil, `imbalanced expression, insufficient operands available for all operators`, false;
                    right_node, left_node := pop_unsafe(&eval), pop_unsafe(&eval);

                    nullable = left_node.nullable || right_node.nullable;

                    first_pos = marry_slices(left_node.first_pos, first_pos);
                    first_pos = marry_slices(right_node.first_pos, first_pos);

                    last_pos = marry_slices(left_node.last_pos, last_pos);
                    last_pos = marry_slices(right_node.last_pos, last_pos);

                    push_unsafe(&eval, current_node);

                case .CONCAT:
                    if eval.head == 1 do return nil, `imbalanced expression, insufficient operands available for all operators`, false;
                    right_node, left_node := pop_unsafe(&eval), pop_unsafe(&eval);

                    nullable = left_node.nullable && right_node.nullable;

                    if(left_node.nullable)
                    {
                        first_pos = marry_slices(left_node.first_pos, first_pos);
                        first_pos = marry_slices(right_node.first_pos, first_pos);
                    }
                    else
                    {
                        first_pos = left_node.first_pos;
                    }

                    if(right_node.nullable)
                    {
                        last_pos = marry_slices(left_node.last_pos, last_pos);
                        last_pos = marry_slices(right_node.last_pos, last_pos);
                    }
                    else
                    {
                        last_pos = right_node.last_pos;
                    }

                    compute_follow_pos(right_node.first_pos, left_node.last_pos);

                    push_unsafe(&eval, current_node);
            }
        }

        if DEBUG do fmt.println("Symbolic evaluation finished!");
    }

    operand_count, transition_count, character_count, total_size :int;

    { // calculate state machine size
        if DEBUG do fmt.println("Calculating size of table started!");

        total_operand_size, total_transition_size, total_character_size :int;

        operand_count = operands.head;
        for i := 0; i < operand_count; i += 1
        {
            operand := #no_bounds_check operands.elements[i];
            temp_transition_count := len(operand.follow_pos);
            transition_count += temp_transition_count;
            for k := 0; k < temp_transition_count; k += 1
            {
                transition := #no_bounds_check operand.follow_pos[k];
                character_value := transition.token.character_value;
                if character_class, ok := character_value.(Character_Class); ok
                {
                    character_count += len(character_class.characters);
                }
            }
        }

        total_size = operand_count * size_of(Table_Entry) + transition_count * size_of(Transition) + character_count * size_of(Character);

        if DEBUG do fmt.println("Calculating size of tables finished! Table is", total_size, "bytes wide!");
    }

    { // table generation
        if DEBUG do fmt.println("Table generation started!");

        // allocate the memory for the state machine and define the distinct regions of the state machine
        regex_arena := cast(^Table_Entry)mem.alloc(size_of(u8) * total_size);
        transition_arena := cast(^Transition)mem.ptr_offset(regex_arena, operand_count);
        character_arena := cast(^Character)mem.ptr_offset(transition_arena, transition_count);

        table = mem.slice_ptr(regex_arena, operand_count);
        table_stack := Stack(Table_Entry){0, table};
        transition_stack := Stack(Transition){0, mem.slice_ptr(transition_arena, transition_count)};
        character_stack := Stack(Character){0, mem.slice_ptr(character_arena, character_count)};

        for i := 0; i < operands.head; i += 1
        {
            operand := #no_bounds_check operands.elements[i];

            transitions_start := transition_stack.head;

            num_jumps := len(operand.follow_pos);
            for k := 0; k < num_jumps; k += 1
            {
                jump := #no_bounds_check operand.follow_pos[k];

                character_value := jump.token.character_value;
                if character_class, ok := character_value.(Character_Class); ok
                {
                    characters_start := character_stack.head;

                    for character in character_class.characters
                    {
                        push_unsafe(&character_stack, character);
                    }

                    character_value = Character_Class{#no_bounds_check character_stack.elements[characters_start : character_stack.head], character_class.negated};
                }

                push_unsafe(&transition_stack, Transition{character_value, jump.position, jump.token.region_name});
            }

            push_unsafe(&table_stack, Table_Entry{#no_bounds_check transition_stack.elements[transitions_start : transition_stack.head]});
        }

        if DEBUG do fmt.println("Table generation finished!");
    }

    if DEBUG
    {
        print_character :: proc(character :Character)
        {
            using character;
            #partial switch type
            {
                case .EXACT:
                    switch min_rune
                    {
                        case '\a':
                            fmt.print("\\a");

                        case '\b':
                            fmt.print("\\b");
                            
                        case '\t':
                            fmt.print("\\t");

                        case '\r':
                            fmt.print("\\r");

                        case '\f':
                            fmt.print("\\f");

                        case '\n':
                            fmt.print("\\n");

                        case '\e':
                            fmt.print("\\e");

                        case:
                            if min_rune == '('
                            || min_rune == ')'
                            || min_rune == '{'
                            || min_rune == '}'
                            || min_rune == '['
                            || min_rune == ']'
                            || min_rune == '|'
                            || min_rune == '*'
                            || min_rune == '?'
                            || min_rune == '+'
                            || min_rune == '\\'
                            || min_rune == '.' do fmt.print('\\');
                            fmt.print(min_rune);
                    }

                case .NON_MATCHING:
                    fmt.print(min_rune);

                case:
                    if min_rune != '.' do fmt.print('\\');
                    fmt.print(min_rune);
            }
        }

        print_character_class :: proc(class :Character_Class)
        {
            fmt.print('[');
                    
            if class.negated do fmt.print('^');

            for character in class.characters
            {
                using character;
                #partial switch type 
                {
                    case .EXACT:
                        switch min_rune
                        {
                            case '\a':
                                fmt.print("\\a");

                            case '\b':
                                fmt.print("\\b");

                            case '\t':
                                fmt.print("\\t");

                            case '\r':
                                fmt.print("\\r");

                            case '\f':
                                fmt.print("\\f");

                            case '\n':
                                fmt.print("\\n");

                            case '\e':
                                fmt.print("\\e");

                            case:
                                if min_rune == ']'
                                || min_rune == '-'
                                || min_rune == '\\'
                                || min_rune == '.' do fmt.print('\\');
                                fmt.print(min_rune);
                        }

                    case .RANGE:
                        fmt.print(min_rune);
                        fmt.print("-");
                        fmt.print(max_rune);

                    case:
                        if min_rune != '.' do fmt.print('\\');
                        fmt.print(min_rune);
                }
            }

            fmt.print(']');
        }

        fmt.println("\nRegex:\n");
        for i := 0; i < token_stack.head; i += 1
        {
            switch character_value in token_stack.elements[i].character_value
            {
                case Character:
                    print_character(character_value);

                case Character_Class:
                    print_character_class(character_value);
            }
        }
        fmt.println(); fmt.println();

        fmt.println("RPN:\n");
        for i := 0; i < rpn.head; i += 1
        {
            node := rpn.elements[i];
            if node.precedence != .OPERAND do
            switch node.operation
            {
                case .ALTERN:
                    fmt.print('|');
                    continue;

                case .CONCAT:
                    fmt.print('.');
                    continue;

                case .KLEENE:
                    fmt.print('*');
                    continue;

                case .EXIST:
                    fmt.print('?');
                    continue;

                case .REPEAT:
                    fmt.print('+');
                    continue;
            }

            token := node.token;
            switch character_value in token.character_value
            {
                case Character:
                    print_character(character_value);

                case Character_Class:
                    print_character_class(character_value);
            }
        }
        fmt.println(); fmt.println();

        fmt.println("STATE MACHINE:\n");
        for entry, index in table
        {
            token := operands.elements[index].token;
            temp_name := token.region_name;
            name := from_region32(temp_name);

            fmt.print(index, ' ');
            switch character_value in token.character_value
            {
                case Character:
                    print_character(character_value);
                case Character_Class:
                    print_character_class(character_value);
            }
            fmt.println(' ', name);

            for transition in entry.transitions
            {
                fmt.print("    ");
                switch character_value in transition.character_value
                {
                    case Character:
                        print_character(character_value);
                    case Character_Class:
                        print_character_class(character_value);
                }
                fmt.println(" goto", transition.jump);
            }
            fmt.println();
        }
    }

    return;
}

match :: proc(regex :^[]Table_Entry, index :int, character :rune) -> (new_index :int, region_name :u128, ok :bool)
{
    is_number :: proc(character :rune) -> bool
    {
        return character >= '0' && character <= '9';
    }

    is_vertical_whitespace :: proc(character :rune) -> bool
    {
        return character >= '\u000A' && character <= '\u000D' || character == '\u2028' || character == '\u2029';
    }

    is_match :: proc(character_value :^Character, character :rune) -> bool
    {
        #partial switch character_value.type
        {
            case .EXACT:
                return character == character_value.min_rune;

            case .RANGE:
                return character >= character_value.min_rune && character <= character_value.max_rune;

            case .NUM:
                return is_number(character);

            case .NOT_NUM:
                return !is_number(character);

            case .LOWER:
                return unicode.is_lower(character);

            case .NOT_LOWER:
                return !unicode.is_lower(character);

            case .UPPER:
                return unicode.is_upper(character);

            case .NOT_UPPER:
                return !unicode.is_upper(character);

            case .WORD:
                return is_number(character) || unicode.is_alpha(character) || character == '_';

            case .NOT_WORD:
                return !(is_number(character) || unicode.is_alpha(character) || character == '_');

            case .WHITESPACE:
                return unicode.is_white_space(character);

            case .NOT_WHITESPACE:
                return !unicode.is_white_space(character);

            case .VERTICAL_WHITESPACE:
                return is_vertical_whitespace(character);

            case .NOT_VERTICAL_WHITESPACE:
                return !is_vertical_whitespace(character);

            case .HORIZONTAL_WHITESPACE:
                return !is_vertical_whitespace(character) && unicode.is_white_space(character);

            case .NOT_HORIZONTAL_WHITESPACE:
                return is_vertical_whitespace(character) && !unicode.is_white_space(character);
        }

        return false;
    }

    entry := &regex[index];

    num_entries := len(entry.transitions);

    for i := 0; i < num_entries; i += 1
    {
        transition := #no_bounds_check &entry.transitions[i];

        jump := transition.jump;
        region_name := transition.region_name;

        switch character_value in &transition.character_value
        {
            case Character:
                if is_match(character_value, character) do return jump, region_name, true;

            case Character_Class:
                characters := &character_value.characters;
                num_characters := len(characters);

                negated := character_value.negated;

                for k := 0; k < num_characters; k += 1
                {
                    if negated != is_match(#no_bounds_check &characters[k], character) do return jump, region_name, true;
                }
        }
    }

    fmt.println();
    fmt.println("broke at", index, "because of", character);
    panic("YOU BROKE ME!");

    return index, 0, false;
}

DEBUG :: false;

main :: proc()
{
    iter :i64 = 10_000;
    if DEBUG do iter = 1;

    if !DEBUG // 10k wide regex
    { 
        start := time.now();

        for i :i64 = 0; i < iter; i += 1
        {
            // i am unsure if this actually compiles correctly with the default temp allocator because it's so large
            regex, _, _ := compile_regex(`((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)`);
            // there is some issue with the default temp allocator where sometimes when it tries to compile the 10k regex the program will crash if this is not done
            free_all(context.temp_allocator);
            defer delete(regex);
        }

        end := time.now();
        total := (end._nsec - start._nsec)/iter;
        fmt.println("\n\nDid not crash. Ran for an average of", total, "ns /", cast(f32)total/1_000_000, "ms.\n\n");
    }

    { // matching
        regex, _, _ := compile_regex(`abc((def|[ghi])*|( [a-zA-Z0-9_]+)+\. and this is to go even further beyond\.)`);
        defer delete(regex);

        start := time.now();

        for i :i64 = 0; i < iter; i += 1
        {
            test_input := "abc hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world hello word hello world. and this is to go even further beyond.#";

            index := 0;
            region :u128;
            ok :bool;
            for character in test_input
            {
                index, region, ok = match(&regex, index, character);
            }
        }

        end := time.now();
        total := (end._nsec - start._nsec)/iter;
        fmt.println("\n\nDid not crash. Ran for an average of", total, "ns /", cast(f32)total/1_000_000, "ms.\n\n");
    }

    {
        regex, error, ok := compile_regex(`{nest:my {ing:super }nested {ed:regex }engine}`);
        if !ok do panic(error);
        defer delete(regex);

        if ok
        {
            test_input := "my super nested regex engine#";

            index := 0;
            region :u128;
            nest := make_temp_stack(rune, 50);
            ing := make_temp_stack(rune, 50);
            ed := make_temp_stack(rune, 50);
            for character in test_input
            {
                index, region, _ = match(&regex, index, character);
                if region == to_region32("nest") do push(&nest, character);
                if region == to_region32("ing") do push(&ing, character);
                if region == to_region32("ed") do push(&ed, character);
                if region == to_region32("accept") do fmt.println("\nInput accepted.");
            }

            fmt.println();
            for i := 0; i < nest.head; i += 1
            {
                fmt.print(nest.elements[i]);
            }

            fmt.println();
            for i := 0; i < ing.head; i += 1
            {
                fmt.print(ing.elements[i]);
            }

            fmt.println();
            for i := 0; i < ed.head; i += 1
            {
                fmt.print(ed.elements[i]);
            }
        }
    }

    fmt.println("\n\nDid not crash.");
}
