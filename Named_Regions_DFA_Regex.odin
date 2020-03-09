package main

import "core:fmt"
import "core:time"
import "core:runtime"
import "core:unicode"

Stack :: struct(T :typeid)
{
    head :int,
    elements :[]T,
}

// if these stack functions are inlined the program will always crash during the set up phase for lexing
make_stack :: inline proc($T :typeid, len :int, allocator := context.temp_allocator) -> (stack :Stack(T))
{
    using stack;
    head = 0;
    elements = make([]T, len, allocator);
    return;
}

push :: inline proc(using stack :^Stack($T), element :T)
{
    elements[head] = element;
    head += 1;
}

pop :: inline proc(using stack :^Stack($T)) -> (element :T)
{
    head -= 1;
    element = elements[head];
    return;
}

peek :: inline proc(using stack :^Stack($T)) -> (element :T)
{
    element = elements[head - 1];
    return;
}

peek_pointer :: inline proc(using stack :^Stack($T)) -> (element :^T)
{
    element = &elements[head - 1];
    return;
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
    condition :Token,
    jump :int,
}

Table_Entry :: struct
{
    transitions :[]Transition,
}

make_table_entry :: inline proc(transition_count :int, allocator := context.allocator) -> (entry :Table_Entry)
{
    entry.transitions = make([]Transition, transition_count, allocator);
    return;
}

b32_slice :: proc(text :[]u8) -> (out :u128)
{
    for character, index in text
    {
        to_bits :u128 = cast(u128)character & 0b000_11111;
        out |= to_bits << cast(u128)(5 * index);
    }
    return;
}

b32_string :: proc(text :string) -> (out :u128)
{
    for character, index in text
    {
        to_bits :u128 = cast(u128)character & 0b000_11111;
        out |= to_bits << cast(u128)(5 * index);
    }

    return;
}

to_b32 :: proc{b32_slice, b32_string};

from_b32 :: proc(value :u128) -> (out :[]rune)
{
    stack := make_stack(rune, 25);
    for i := 0; i < 26; i += 1
    {
        character := cast(u8)(0b011_00000 | (0b000_11111 & (value >> cast(u128)(5 * i))));
        if character == 0b011_11111 do character = 0b010_11111;
        if character == 0b011_00000 do break;
        push(&stack, cast(rune)character);
    }
    out = stack.elements[0 : stack.head];
    return;
}

compile_regex :: proc(regex :string) -> (table :[]Table_Entry)
{
    name_start, name_accept := to_b32("start"), to_b32("accept");

    regex_length := len(regex) + 4; // the 4 is because of the 4 characters in: "s(" + regex + ")#"

    if regex_length % 2 != 0 do regex_length += 1; // for some reason the program crashes during lexing if this value is odd

    if DEBUG do fmt.println("Regex length:", regex_length);

    token_stack := make_stack(Token, regex_length);

    { // lexing
        if DEBUG do fmt.println("Lexing started!");

        // always crashes here on -opt:1
        push(&token_stack, Token{Character{'S', 0, .EXACT}, token_stack.head, name_start});
        push(&token_stack, Token{Character{'(', 0, .NON_MATCHING}, token_stack.head, 0});

        Lex_State :: enum i8
        {
            NORMAL,
            NAMING,
            ESCAPE,
            CLASS_START,
            CLASS,
            CLASS_RANGE,
            CLASS_ESCAPE,
        };
        state := Lex_State.NORMAL;

        region_name_stack := make_stack(u128, regex_length);
        // crashes here on -opt:2 and -opt:3 if the regex_length variable is an odd value
        push(&region_name_stack, 0);
        region_stack := make_stack(u8, 25);

        class_stack := make_stack(Character, regex_length);
        negated := false;


        for current_rune in regex
        {
            switch state
            {
                case .NORMAL:
                    if DEBUG do fmt.println(state, current_rune);

                    switch current_rune
                    {
                        case '{':
                            state = .NAMING;
                            region_stack.head = 0;
                        
                        case '}':
                            pop(&region_name_stack);

                        case '\\':
                            state = .ESCAPE;

                        case '[':
                            state = .CLASS_START;
                            class_stack.head = 0;
                            negated = false;

                        case '(':
                            push(&token_stack, Token{Character{current_rune, 0, .NON_MATCHING}, token_stack.head, peek(&region_name_stack)});

                        case ')':
                            push(&token_stack, Token{Character{current_rune, 0, .NON_MATCHING}, token_stack.head, peek(&region_name_stack)});

                        case '|':
                            push(&token_stack, Token{Character{current_rune, 0, .NON_MATCHING}, token_stack.head, peek(&region_name_stack)});

                        case '*':
                            push(&token_stack, Token{Character{current_rune, 0, .NON_MATCHING}, token_stack.head, peek(&region_name_stack)});

                        case '?':
                            push(&token_stack, Token{Character{current_rune, 0, .NON_MATCHING}, token_stack.head, peek(&region_name_stack)});

                        case '+':
                            push(&token_stack, Token{Character{current_rune, 0, .NON_MATCHING}, token_stack.head, peek(&region_name_stack)});

                        case '.':
                            push(&token_stack, Token{Character{current_rune, 0, .NOT_VERTICAL_WHITESPACE}, token_stack.head, peek(&region_name_stack)});

                        case:
                            push(&token_stack, Token{Character{current_rune, 0, .EXACT}, token_stack.head, peek(&region_name_stack)});
                    }

                case .NAMING:
                    if DEBUG do fmt.println(state, current_rune);

                    switch current_rune
                    {
                        case ':':
                            state = .NORMAL;
                            push(&region_name_stack, to_b32(region_stack.elements[0 : region_stack.head]));

                        case:
                            push(&region_stack, cast(u8)current_rune);
                    }

                case .ESCAPE:
                    if DEBUG do fmt.println(state, current_rune);

                    state = .NORMAL;
                    switch current_rune
                    {
                        case 'd':
                            push(&token_stack, Token{Character{current_rune, 0, .NUM}, token_stack.head, peek(&region_name_stack)});

                        case 'D':
                            push(&token_stack, Token{Character{current_rune, 0, .NOT_NUM}, token_stack.head, peek(&region_name_stack)});

                        case 'l':
                            push(&token_stack, Token{Character{current_rune, 0, .LOWER}, token_stack.head, peek(&region_name_stack)});

                        case 'L':
                            push(&token_stack, Token{Character{current_rune, 0, .NOT_LOWER}, token_stack.head, peek(&region_name_stack)});

                        case 'u':
                            push(&token_stack, Token{Character{current_rune, 0, .UPPER}, token_stack.head, peek(&region_name_stack)});

                        case 'U':
                            push(&token_stack, Token{Character{current_rune, 0, .NOT_UPPER}, token_stack.head, peek(&region_name_stack)});

                        case 'w':
                            push(&token_stack, Token{Character{current_rune, 0, .WORD}, token_stack.head, peek(&region_name_stack)});

                        case 'W':
                            push(&token_stack, Token{Character{current_rune, 0, .NOT_WORD}, token_stack.head, peek(&region_name_stack)});

                        case 's':
                            push(&token_stack, Token{Character{current_rune, 0, .WHITESPACE}, token_stack.head, peek(&region_name_stack)});

                        case 'S':
                            push(&token_stack, Token{Character{current_rune, 0, .NOT_WHITESPACE}, token_stack.head, peek(&region_name_stack)});

                        case 'v':
                            push(&token_stack, Token{Character{current_rune, 0, .VERTICAL_WHITESPACE}, token_stack.head, peek(&region_name_stack)});

                        case 'V':
                            push(&token_stack, Token{Character{current_rune, 0, .NOT_VERTICAL_WHITESPACE}, token_stack.head, peek(&region_name_stack)});

                        case 'h':
                            push(&token_stack, Token{Character{current_rune, 0, .HORIZONTAL_WHITESPACE}, token_stack.head, peek(&region_name_stack)});

                        case 'H':
                            push(&token_stack, Token{Character{current_rune, 0, .NOT_HORIZONTAL_WHITESPACE}, token_stack.head, peek(&region_name_stack)});

                        case 'a': // bell
                            push(&token_stack, Token{Character{'\a', 0, .EXACT}, token_stack.head, peek(&region_name_stack)});

                        case 'b': // backspace
                            push(&token_stack, Token{Character{'\b', 0, .EXACT}, token_stack.head, peek(&region_name_stack)});

                        case 't': // tab
                            push(&token_stack, Token{Character{'\t', 0, .EXACT}, token_stack.head, peek(&region_name_stack)});

                        case 'r': // carriage return
                            push(&token_stack, Token{Character{'\r', 0, .EXACT}, token_stack.head, peek(&region_name_stack)});

                        case 'f': // form feed
                            push(&token_stack, Token{Character{'\f', 0, .EXACT}, token_stack.head, peek(&region_name_stack)});

                        case 'n': // new line
                            push(&token_stack, Token{Character{'\n', 0, .EXACT}, token_stack.head, peek(&region_name_stack)});

                        case 'e': // escape
                            push(&token_stack, Token{Character{'\e', 0, .EXACT}, token_stack.head, peek(&region_name_stack)});

                        case:
                            push(&token_stack, Token{Character{current_rune, 0, .EXACT}, token_stack.head, peek(&region_name_stack)});
                    }

                case .CLASS_START:
                    if DEBUG do fmt.println(state, current_rune);

                    switch current_rune
                    {
                        case '^':
                            state = .CLASS;
                            negated = true;

                        case '\\':
                            state = .CLASS_ESCAPE;

                        case '.':
                            push(&class_stack, Character{current_rune, 0, .NOT_VERTICAL_WHITESPACE});

                        case ']':
                            state = .NORMAL;
                            temp_slice := make([]Character, class_stack.head, context.temp_allocator);
                            runtime.copy_slice(temp_slice, class_stack.elements[0 : class_stack.head]);
                            push(&token_stack, Token{Character_Class{temp_slice, negated}, token_stack.head, peek(&region_name_stack)});

                        case:
                            state = .CLASS;
                            push(&class_stack, Character{current_rune, 0, .EXACT});
                    }

                case .CLASS:
                    if DEBUG do fmt.println(state, current_rune);

                    switch current_rune
                    {
                        case '-':
                            state = .CLASS_RANGE;

                        case '\\':
                            state = .CLASS_ESCAPE;

                        case '.':
                            push(&class_stack, Character{current_rune, 0, .NOT_VERTICAL_WHITESPACE});

                        case ']':
                            state = .NORMAL;
                            temp_slice := make([]Character, class_stack.head, context.temp_allocator);
                            runtime.copy_slice(temp_slice, class_stack.elements[0 : class_stack.head]);
                            push(&token_stack, Token{Character_Class{temp_slice, negated}, token_stack.head, peek(&region_name_stack)});


                        case:
                            push(&class_stack, Character{current_rune, 0, .EXACT});
                    }

                case .CLASS_RANGE:
                    if DEBUG do fmt.println(state, current_rune);

                    state = .CLASS;
                    character := &class_stack.elements[class_stack.head - 1];
                    character.max_rune = current_rune;
                    character.type = .RANGE;

                case .CLASS_ESCAPE:
                    if DEBUG do fmt.println(state, current_rune);

                    state = .CLASS;
                    switch current_rune
                    {
                        case 'd':
                            push(&class_stack, Character{current_rune, 0, .NUM});

                        case 'D':
                            push(&class_stack, Character{current_rune, 0, .NOT_NUM});

                        case 'l':
                            push(&class_stack, Character{current_rune, 0, .LOWER});

                        case 'L':
                            push(&class_stack, Character{current_rune, 0, .NOT_LOWER});

                        case 'u':
                            push(&class_stack, Character{current_rune, 0, .UPPER});

                        case 'U':
                            push(&class_stack, Character{current_rune, 0, .NOT_UPPER});

                        case 'w':
                            push(&class_stack, Character{current_rune, 0, .WORD});

                        case 'W':
                            push(&class_stack, Character{current_rune, 0, .NOT_WORD});

                        case 's':
                            push(&class_stack, Character{current_rune, 0, .WHITESPACE});

                        case 'S':
                            push(&class_stack, Character{current_rune, 0, .NOT_WHITESPACE});

                        case 'v':
                            push(&class_stack, Character{current_rune, 0, .VERTICAL_WHITESPACE});

                        case 'V':
                            push(&class_stack, Character{current_rune, 0, .NOT_VERTICAL_WHITESPACE});

                        case 'h':
                            push(&class_stack, Character{current_rune, 0, .HORIZONTAL_WHITESPACE});

                        case 'H':
                            push(&class_stack, Character{current_rune, 0, .NOT_HORIZONTAL_WHITESPACE});

                        case 'a': // bell
                            push(&class_stack, Character{'\a', 0, .EXACT});

                        case 'b': // backspace
                            push(&class_stack, Character{'\b', 0, .EXACT});

                        case 't': // tab
                            push(&class_stack, Character{'\t', 0, .EXACT});

                        case 'r': // carriage return
                            push(&class_stack, Character{'\r', 0, .EXACT});

                        case 'f': // form feed
                            push(&class_stack, Character{'\f', 0, .EXACT});

                        case 'n': // new line
                            push(&class_stack, Character{'\n', 0, .EXACT});

                        case 'e': // escape
                            push(&class_stack, Character{'\e', 0, .EXACT});

                        case:
                            push(&class_stack, Character{current_rune, 0, .EXACT});
                    }
            }
        }

        push(&token_stack, Token{Character{')', 0, .NON_MATCHING}, token_stack.head, 0});
        push(&token_stack, Token{Character{'#', 0, .EXACT}, token_stack.head, name_accept});

        if DEBUG do fmt.println("Lexing finished!");
    }

    regex_length = token_stack.head;
    tokens := token_stack.elements[0 : regex_length];

    // double the length to account for the implicit concat(.) operator
    // and plus one to account for the success state(#)
    max_nodes := regex_length * 2 + 1;
    max_operands := regex_length + 1;

    nodes := make_stack(Node, max_nodes);

    rpn := make_stack(^Node, max_nodes);
    ops := make_stack(^Node, regex_length);

    operands := make_stack(^Node, max_operands);
    eval := make_stack(^Node, max_nodes);

    { // parsing
        if DEBUG do fmt.println("Parsing started!");

        shunting_yard :: proc(using current_node :^Node, rpn :^Stack(^Node), ops :^Stack(^Node))
        {
            switch
            {
                case precedence == .OPERAND:
                    push(rpn, current_node);

                case precedence == .OPAREN:
                    push(ops, current_node);

                case precedence == .ALTERN
                || precedence == .CONCAT
                || precedence == .UNARY:
                    for
                    {
                        if ops.head == 0 || precedence > peek(ops).precedence
                        {
                            push(ops, current_node);
                            break;
                        }
                        else
                        {
                            push(rpn, pop(ops));
                        }
                    }

                case precedence == .CLOPAREN:
                    for
                    {
                        if peek(ops).precedence != .OPAREN
                        {
                            push(rpn, pop(ops));
                        }
                        else
                        {
                            pop(ops);
                            break;
                        }
                    }
            }
        }

        using current_node :Node;
        precedence = .INVALID_PRECEDENCE;

        for i := 0; i < regex_length; i += 1
        {
            current_token := &tokens[i];

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
                push(&nodes, CONCAT_NODE);
                shunting_yard(peek_pointer(&nodes), &rpn, &ops);
            }

            push(&nodes, current_node);
            shunting_yard(peek_pointer(&nodes), &rpn, &ops);
        }

        for ops.head != 0
        {
            push(&rpn, pop(&ops));
        }

        if DEBUG do fmt.println("Parsing finished!");
    }

    { // symbolic evaluation
        if DEBUG do fmt.println("Symbolic evaluation started!");

        compute_follow_pos :: proc(first_pos :[]^Node, leaves :[]^Node)
        {
            length := len(leaves);
            for i := 0; i < length; i += 1
            {
                leaf := leaves[i];

                leaf.follow_pos = marry_slices(first_pos, leaf.follow_pos);
            }
        }

        marry_slices :: proc(left :[]$T, right :[]T) -> (out :[]T)
        {
            lenl, lenr := len(left), len(right);
            lenlr := lenl + lenr;
            out = make([]T, lenlr, context.temp_allocator);

            outl := out[0 : lenl];
            runtime.copy_slice(out, left);

            outr := out[lenl : lenlr];
            runtime.copy_slice(outr, right);

            return;
        }

        for i := 0; i < rpn.head; i += 1
        {
            using current_node := rpn.elements[i];

            #partial switch precedence
            {
                case .OPERAND:
                    nullable = false;

                    first_pos = make([]^Node, 1, context.temp_allocator);
                    first_pos[0] = current_node;

                    last_pos = make([]^Node, 1, context.temp_allocator);
                    last_pos[0] = current_node;

                    position = operands.head;

                    push(&operands, current_node);
                    push(&eval, current_node);

                case .UNARY:
                    middle_node := pop(&eval);

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

                    push(&eval, current_node);

                case .ALTERN:
                    right_node, left_node := pop(&eval), pop(&eval);

                    nullable = left_node.nullable || right_node.nullable;

                    first_pos = marry_slices(left_node.first_pos, first_pos);
                    first_pos = marry_slices(right_node.first_pos, first_pos);

                    last_pos = marry_slices(left_node.last_pos, last_pos);
                    last_pos = marry_slices(right_node.last_pos, last_pos);

                    push(&eval, current_node);

                case .CONCAT:
                    right_node, left_node := pop(&eval), pop(&eval);

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

                    push(&eval, current_node);
            }
        }

        if DEBUG do fmt.println("Symbolic evaluation finished!");
    }

    // TODO: make the table generation format the table in memory in a way that's easy to free
    { // table generation
        if DEBUG do fmt.println("Table generation started!");

        table = make([]Table_Entry, operands.head);

        for i := 0; i < operands.head; i += 1
        {
            operand := operands.elements[i];

            table[i] = make_table_entry(len(operand.follow_pos));

            for jump, index in operand.follow_pos
            {
                transition := &table[i].transitions[index];
                jump_token := jump.token;

                transition.jump = jump.position;
                transition.condition = jump_token^;

                #partial switch character_value in transition.condition.character_value
                {
                    case Character_Class:
                        class_length := len(character_value.characters);
                        temp_slice := make([]Character, class_length);
                        runtime.copy_slice(temp_slice, character_value.characters);
                        
                        negated := character_value.negated;

                        transition.condition.character_value = Character_Class{temp_slice, negated};
                }
            }
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
            name := from_b32(temp_name);

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
                condition := transition.condition;
                fmt.print("    ");
                switch character_value in condition.character_value
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
        return character == '0'
        || character == '1'
        || character == '2'
        || character == '3'
        || character == '4'
        || character == '5'
        || character == '6'
        || character == '7'
        || character == '8'
        || character == '9';
    }

    is_vertical_whitespace :: proc(character :rune) -> bool
    {
        return character >= '\u000A' && character <= '\u000D' || character == '\u2028' || character == '\u2029';
    }

    is_match :: proc(condition :Character, character :rune) -> bool
    {
        #partial switch condition.type
        {
            case .EXACT:
                return character == condition.min_rune;

            case .RANGE:
                return character >= condition.min_rune && character <= condition.max_rune;

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
        transition := entry.transitions[i];

        jump := transition.jump;
        region_name := transition.condition.region_name;

        switch character_value in transition.condition.character_value
        {
            case Character:
                if is_match(character_value, character) do return jump, region_name, true;

            case Character_Class:
                characters := character_value.characters;
                num_characters := len(characters);

                negated := character_value.negated;

                for k := 0; k < num_characters; k += 1
                {
                    condition := characters[k];
                    matched := is_match(condition, character);
                    if !negated && matched || negated && !matched do return jump, region_name, true;
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
    iter :i64 = 1000;
    if DEBUG do iter = 1;

    if !DEBUG // 10k wide regex
    { 
        start := time.now();

        for i :i64 = 0; i < iter; i += 1
        {
            compile_regex("((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)((abc(def|ghi(jkl|mnop)))+(zabc(def|ghi(jkl|mnop)))+)");
        }

        end := time.now();
        total := (end._nsec - start._nsec)/iter;
        fmt.println("\n\nDid not crash. Ran for", total, "ns /", cast(f32)total/1_000_000, "ms.\n\n");
    }

    { // matching
        regex := compile_regex("abc((def|[ghi])*|( \\w+)+\\. and this is to go even further beyond.)");
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
        fmt.println("\n\nDid not crash. Ran for", total, "ns /", cast(f32)total/1_000_000, "ms.\n\n");
    }

    regex := compile_regex("{nest:my {ing:super }nested {ed:regex} engine}");

    test_input := "my super nested regex engine#";

    index := 0;
    region :u128;
    ok :bool;
    nest := make_stack(rune, 50);
    ing := make_stack(rune, 50);
    ed := make_stack(rune, 50);
    for character in test_input
    {
        index, region, ok = match(&regex, index, character);
        if region == to_b32("nest") do push(&nest, character);
        if region == to_b32("ing") do push(&ing, character);
        if region == to_b32("ed") do push(&ed, character);
        if region == to_b32("accept") do fmt.println("\nInput accepted.");
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

    fmt.println("\n\nDid not crash.");
}