function noop() { }
const identity = x => x;
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link0;
	let link0_href_value;
	let link1;
	let script0;
	let script0_src_value;
	let script1;
	let t0;
	let title_value;
	let meta2;
	let meta3;
	let meta4;
	let meta4_content_value;
	let style;
	let t1;
	document.title = title_value = /*title*/ ctx[1];

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link0 = element("link");
			link1 = element("link");
			script0 = element("script");
			script1 = element("script");
			t0 = text("(function(w,d,e,u,f,l,n){w[f]=w[f]||function(){(w[f].q=w[f].q||[])\n    .push(arguments);},l=d.createElement(e),l.async=1,l.src=u,\n    n=d.getElementsByTagName(e)[0],n.parentNode.insertBefore(l,n);})\n    (window,document,'script','https://assets.mailerlite.com/js/universal.js','ml');\n    ml('account', '511328');\n");
			meta2 = element("meta");
			meta3 = element("meta");
			meta4 = element("meta");
			style = element("style");
			t1 = text("/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: #027648;\n  --color1: #4C5760;\n  \n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: #111;\n  line-height: 1.5;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1200px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0; /* reset */\n  max-height: 80px;\n}\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1jwgbch', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });

			link0 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			link1 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			script0 = claim_element(head_nodes, "SCRIPT", { src: true, "data-website-id": true });
			var script0_nodes = children(script0);
			script0_nodes.forEach(detach);
			script1 = claim_element(head_nodes, "SCRIPT", {});
			var script1_nodes = children(script1);
			t0 = claim_text(script1_nodes, "(function(w,d,e,u,f,l,n){w[f]=w[f]||function(){(w[f].q=w[f].q||[])\n    .push(arguments);},l=d.createElement(e),l.async=1,l.src=u,\n    n=d.getElementsByTagName(e)[0],n.parentNode.insertBefore(l,n);})\n    (window,document,'script','https://assets.mailerlite.com/js/universal.js','ml');\n    ml('account', '511328');\n");
			script1_nodes.forEach(detach);
			meta2 = claim_element(head_nodes, "META", { property: true, content: true });
			meta3 = claim_element(head_nodes, "META", { property: true, content: true });
			meta4 = claim_element(head_nodes, "META", { property: true, content: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t1 = claim_text(style_nodes, "/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: #027648;\n  --color1: #4C5760;\n  \n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: #111;\n  line-height: 1.5;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1200px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0; /* reset */\n  max-height: 80px;\n}\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link0, "rel", "icon");
			attr(link0, "type", "image/png");
			attr(link0, "sizes", "32x32");
			attr(link0, "href", link0_href_value = /*favicon*/ ctx[0].url);
			attr(link1, "rel", "preconnect");
			attr(link1, "href", "https://fonts.bunny.net");
			script0.async = true;
			if (!src_url_equal(script0.src, script0_src_value = "https://analytics.umami.is/script.js")) attr(script0, "src", script0_src_value);
			attr(script0, "data-website-id", "541fddec-8517-45e6-b5e5-6a9e36cb83c3");
			attr(meta2, "property", "og:title");
			attr(meta2, "content", /*title*/ ctx[1]);
			attr(meta3, "property", "og:type");
			attr(meta3, "content", "article");
			attr(meta4, "property", "og:image");
			attr(meta4, "content", meta4_content_value = /*preview_image*/ ctx[2].url);
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, script0);
			append_hydration(document.head, script1);
			append_hydration(script1, t0);
			append_hydration(document.head, meta2);
			append_hydration(document.head, meta3);
			append_hydration(document.head, meta4);
			append_hydration(document.head, style);
			append_hydration(style, t1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*favicon*/ 1 && link0_href_value !== (link0_href_value = /*favicon*/ ctx[0].url)) {
				attr(link0, "href", link0_href_value);
			}

			if (dirty & /*title*/ 2 && title_value !== (title_value = /*title*/ ctx[1])) {
				document.title = title_value;
			}

			if (dirty & /*title*/ 2) {
				attr(meta2, "content", /*title*/ ctx[1]);
			}

			if (dirty & /*preview_image*/ 4 && meta4_content_value !== (meta4_content_value = /*preview_image*/ ctx[2].url)) {
				attr(meta4, "content", meta4_content_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link0);
			detach(link1);
			detach(script0);
			detach(script1);
			detach(meta2);
			detach(meta3);
			detach(meta4);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(3, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(4, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(2, preview_image = $$props.preview_image);
	};

	return [favicon, title, preview_image, color1, color2];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			color1: 3,
			color2: 4,
			favicon: 0,
			title: 1,
			preview_image: 2
		});
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

/* generated by Svelte v3.58.0 */

function create_fragment$1(ctx) {
	let t;

	return {
		c() {
			t = text("/*\n * [Package Error] \"@iconify/svelte@v4.0.1\" could not be built. \n *\n *   [1/5] Verifying package is valid…\n *   [2/5] Installing dependencies from npm…\n *   [3/5] Building package using esinstall…\n *   Running esinstall...\n *   ENOENT: no such file or directory, open '@iconify/svelte/lib/dist/functions.js'\n *   ENOENT: no such file or directory, open '/tmp/cdn/_hJGvglwvKpJhhwWyDAuT/node_modules/@iconify/svelte/lib/dist/functions.js'\n *\n * How to fix:\n *   - If you believe this to be an error in Skypack, file an issue here: https://github.com/skypackjs/skypack-cdn/issues\n *   - If you believe this to be an issue in the package, share this URL with the package authors to help them debug & fix.\n *   - Use https://skypack.dev/ to find a web-friendly alternative to find another package.\n */\n\nconsole.warn(\"[Package Error] \\\"@iconify/svelte@v4.0.1\\\" could not be built. \\n[1/5] Verifying package is valid…\\n[2/5] Installing dependencies from npm…\\n[3/5] Building package using esinstall…\\nRunning esinstall...\\nENOENT: no such file or directory, open '@iconify/svelte/lib/dist/functions.js'\\nENOENT: no such file or directory, open '/tmp/cdn/_hJGvglwvKpJhhwWyDAuT/node_modules/@iconify/svelte/lib/dist/functions.js'\");\nthrow new Error(\"[Package Error] \\\"@iconify/svelte@v4.0.1\\\" could not be built. \");\nexport default null;");
		},
		l(nodes) {
			t = claim_text(nodes, "/*\n * [Package Error] \"@iconify/svelte@v4.0.1\" could not be built. \n *\n *   [1/5] Verifying package is valid…\n *   [2/5] Installing dependencies from npm…\n *   [3/5] Building package using esinstall…\n *   Running esinstall...\n *   ENOENT: no such file or directory, open '@iconify/svelte/lib/dist/functions.js'\n *   ENOENT: no such file or directory, open '/tmp/cdn/_hJGvglwvKpJhhwWyDAuT/node_modules/@iconify/svelte/lib/dist/functions.js'\n *\n * How to fix:\n *   - If you believe this to be an error in Skypack, file an issue here: https://github.com/skypackjs/skypack-cdn/issues\n *   - If you believe this to be an issue in the package, share this URL with the package authors to help them debug & fix.\n *   - Use https://skypack.dev/ to find a web-friendly alternative to find another package.\n */\n\nconsole.warn(\"[Package Error] \\\"@iconify/svelte@v4.0.1\\\" could not be built. \\n[1/5] Verifying package is valid…\\n[2/5] Installing dependencies from npm…\\n[3/5] Building package using esinstall…\\nRunning esinstall...\\nENOENT: no such file or directory, open '@iconify/svelte/lib/dist/functions.js'\\nENOENT: no such file or directory, open '/tmp/cdn/_hJGvglwvKpJhhwWyDAuT/node_modules/@iconify/svelte/lib/dist/functions.js'\");\nthrow new Error(\"[Package Error] \\\"@iconify/svelte@v4.0.1\\\" could not be built. \");\nexport default null;");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[12] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[12] = list[i].link;
	return child_ctx;
}

// (115:6) {#if logo.image.url}
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", {
				src: true,
				alt: true,
				style: true,
				class: true
			});

			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			set_style(img, "max-width", /*logo_width*/ ctx[2] + "px");
			attr(img, "class", "svelte-nnp8i3");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*logo_width*/ 4) {
				set_style(img, "max-width", /*logo_width*/ ctx[2] + "px");
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (121:6) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[12].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-nnp8i3");
			attr(a, "href", a_href_value = /*link*/ ctx[12].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[12].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[12].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (128:6) {#if logo.image.url}
function create_if_block_1(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", {
				class: true,
				src: true,
				alt: true,
				style: true
			});

			this.h();
		},
		h() {
			attr(img, "class", "logo svelte-nnp8i3");
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			set_style(img, "max-width", /*logo_width*/ ctx[2] + "px");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*logo_width*/ 4) {
				set_style(img, "max-width", /*logo_width*/ ctx[2] + "px");
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (139:4) {#if mobileNavOpen}
function create_if_block(ctx) {
	let nav;
	let t;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-nnp8i3");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-nnp8i3");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[10]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2) {
				each_value = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (141:8) {#each site_nav as { link }}
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[12].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[12].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[12].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[12].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$2(ctx) {
	let div2;
	let header;
	let div0;
	let a0;
	let t0;
	let t1_value = /*logo*/ ctx[0].title + "";
	let t1;
	let t2;
	let nav;
	let t3;
	let div1;
	let a1;
	let t4;
	let t5_value = /*logo*/ ctx[0].title + "";
	let t5;
	let t6;
	let button;
	let icon;
	let t7;
	let current;
	let mounted;
	let dispose;
	let if_block0 = /*logo*/ ctx[0].image.url && create_if_block_2(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	let if_block1 = /*logo*/ ctx[0].image.url && create_if_block_1(ctx);

	icon = new Component$1({
			props: { height: "30", icon: "eva:menu-outline" }
		});

	let if_block2 = /*mobileNavOpen*/ ctx[3] && create_if_block(ctx);

	return {
		c() {
			div2 = element("div");
			header = element("header");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			t1 = text(t1_value);
			t2 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t3 = space();
			div1 = element("div");
			a1 = element("a");
			if (if_block1) if_block1.c();
			t4 = space();
			t5 = text(t5_value);
			t6 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t7 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			t0 = claim_space(a0_nodes);
			t1 = claim_text(a0_nodes, t1_value);
			a0_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a1 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			if (if_block1) if_block1.l(a1_nodes);
			t4 = claim_space(a1_nodes);
			t5 = claim_text(a1_nodes, t5_value);
			a1_nodes.forEach(detach);
			t6 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t7 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-nnp8i3");
			attr(nav, "class", "svelte-nnp8i3");
			attr(div0, "class", "desktop-nav svelte-nnp8i3");
			attr(a1, "href", "/");
			attr(a1, "class", "logo svelte-nnp8i3");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-nnp8i3");
			attr(header, "class", "section-container svelte-nnp8i3");
			attr(div2, "class", "section");
			attr(div2, "id", "section-b6b049eb");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, header);
			append_hydration(header, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(a0, t0);
			append_hydration(a0, t1);
			append_hydration(div0, t2);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(header, t3);
			append_hydration(header, div1);
			append_hydration(div1, a1);
			if (if_block1) if_block1.m(a1, null);
			append_hydration(a1, t4);
			append_hydration(a1, t5);
			append_hydration(div1, t6);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t7);
			if (if_block2) if_block2.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[9]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (/*logo*/ ctx[0].image.url) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_2(ctx);
					if_block0.c();
					if_block0.m(a0, t0);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if ((!current || dirty & /*logo*/ 1) && t1_value !== (t1_value = /*logo*/ ctx[0].title + "")) set_data(t1, t1_value);

			if (dirty & /*site_nav*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if (/*logo*/ ctx[0].image.url) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block_1(ctx);
					if_block1.c();
					if_block1.m(a1, t4);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}

			if ((!current || dirty & /*logo*/ 1) && t5_value !== (t5_value = /*logo*/ ctx[0].title + "")) set_data(t5, t5_value);

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			if (if_block0) if_block0.d();
			destroy_each(each_blocks, detaching);
			if (if_block1) if_block1.d();
			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { logo_width } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(3, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(3, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(4, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(5, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(6, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(7, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(8, preview_image = $$props.preview_image);
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('logo_width' in $$props) $$invalidate(2, logo_width = $$props.logo_width);
	};

	return [
		logo,
		site_nav,
		logo_width,
		mobileNavOpen,
		color1,
		color2,
		favicon,
		title,
		preview_image,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$1, create_fragment$2, safe_not_equal, {
			color1: 4,
			color2: 5,
			favicon: 6,
			title: 7,
			preview_image: 8,
			logo: 0,
			site_nav: 1,
			logo_width: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$3(ctx) {
	let div2;
	let div1;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container content svelte-1b9cr7a");
			attr(div1, "class", "section");
			attr(div2, "class", "section");
			attr(div2, "id", "section-917853d6");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(1, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(2, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(5, preview_image = $$props.preview_image);
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
	};

	return [content, color1, color2, favicon, title, preview_image];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$3, safe_not_equal, {
			color1: 1,
			color2: 2,
			favicon: 3,
			title: 4,
			preview_image: 5,
			content: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$4(ctx) {
	let div;
	let section;
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			div = element("div");
			section = element("section");
			img = element("img");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			section = claim_element(div_nodes, "SECTION", { class: true });
			var section_nodes = children(section);

			img = claim_element(section_nodes, "IMG", {
				src: true,
				alt: true,
				style: true,
				class: true
			});

			section_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[0].alt);
			set_style(img, "max-height", /*max_height*/ ctx[1] + "px");
			attr(img, "class", "svelte-1qe5oiy");
			attr(section, "class", "section-container svelte-1qe5oiy");
			attr(div, "class", "section");
			attr(div, "id", "section-1be78ed5");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, section);
			append_hydration(section, img);
		},
		p(ctx, [dirty]) {
			if (dirty & /*image*/ 1 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 1 && img_alt_value !== (img_alt_value = /*image*/ ctx[0].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*max_height*/ 2) {
				set_style(img, "max-height", /*max_height*/ ctx[1] + "px");
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { image } = $$props;
	let { max_height } = $$props;
	let { caption } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(2, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(3, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(5, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(6, preview_image = $$props.preview_image);
		if ('image' in $$props) $$invalidate(0, image = $$props.image);
		if ('max_height' in $$props) $$invalidate(1, max_height = $$props.max_height);
		if ('caption' in $$props) $$invalidate(7, caption = $$props.caption);
	};

	return [image, max_height, color1, color2, favicon, title, preview_image, caption];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$4, safe_not_equal, {
			color1: 2,
			color2: 3,
			favicon: 4,
			title: 5,
			preview_image: 6,
			image: 0,
			max_height: 1,
			caption: 7
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$5(ctx) {
	let div2;
	let div1;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container content svelte-1b9cr7a");
			attr(div1, "class", "section");
			attr(div2, "class", "section");
			attr(div2, "id", "section-87500d52");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(1, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(2, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(5, preview_image = $$props.preview_image);
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
	};

	return [content, color1, color2, favicon, title, preview_image];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$5, safe_not_equal, {
			color1: 1,
			color2: 2,
			favicon: 3,
			title: 4,
			preview_image: 5,
			content: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$6(ctx) {
	let div;
	let section;
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			div = element("div");
			section = element("section");
			img = element("img");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			section = claim_element(div_nodes, "SECTION", { class: true });
			var section_nodes = children(section);

			img = claim_element(section_nodes, "IMG", {
				src: true,
				alt: true,
				style: true,
				class: true
			});

			section_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[0].alt);
			set_style(img, "max-height", /*max_height*/ ctx[1] + "px");
			attr(img, "class", "svelte-1qe5oiy");
			attr(section, "class", "section-container svelte-1qe5oiy");
			attr(div, "class", "section");
			attr(div, "id", "section-5fdaa7e0");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, section);
			append_hydration(section, img);
		},
		p(ctx, [dirty]) {
			if (dirty & /*image*/ 1 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 1 && img_alt_value !== (img_alt_value = /*image*/ ctx[0].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*max_height*/ 2) {
				set_style(img, "max-height", /*max_height*/ ctx[1] + "px");
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { image } = $$props;
	let { max_height } = $$props;
	let { caption } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(2, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(3, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(5, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(6, preview_image = $$props.preview_image);
		if ('image' in $$props) $$invalidate(0, image = $$props.image);
		if ('max_height' in $$props) $$invalidate(1, max_height = $$props.max_height);
		if ('caption' in $$props) $$invalidate(7, caption = $$props.caption);
	};

	return [image, max_height, color1, color2, favicon, title, preview_image, caption];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$6, safe_not_equal, {
			color1: 2,
			color2: 3,
			favicon: 4,
			title: 5,
			preview_image: 6,
			image: 0,
			max_height: 1,
			caption: 7
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$7(ctx) {
	let div2;
	let div1;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container content svelte-1b9cr7a");
			attr(div1, "class", "section");
			attr(div2, "class", "section");
			attr(div2, "id", "section-b26be9f9");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(1, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(2, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(5, preview_image = $$props.preview_image);
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
	};

	return [content, color1, color2, favicon, title, preview_image];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$7, safe_not_equal, {
			color1: 1,
			color2: 2,
			favicon: 3,
			title: 4,
			preview_image: 5,
			content: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$8(ctx) {
	let div;
	let aside;
	let h3;
	let raw_value = /*quote*/ ctx[0].html + "";
	let t0;
	let span;
	let t1;

	return {
		c() {
			div = element("div");
			aside = element("aside");
			h3 = element("h3");
			t0 = space();
			span = element("span");
			t1 = text(/*attribution*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			aside = claim_element(div_nodes, "ASIDE", { class: true });
			var aside_nodes = children(aside);
			h3 = claim_element(aside_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			h3_nodes.forEach(detach);
			t0 = claim_space(aside_nodes);
			span = claim_element(aside_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, /*attribution*/ ctx[1]);
			span_nodes.forEach(detach);
			aside_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "heading");
			attr(span, "class", "attribution");
			attr(aside, "class", "section-container svelte-ja2udn");
			attr(div, "class", "section");
			attr(div, "id", "section-c380b019");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, aside);
			append_hydration(aside, h3);
			h3.innerHTML = raw_value;
			append_hydration(aside, t0);
			append_hydration(aside, span);
			append_hydration(span, t1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*quote*/ 1 && raw_value !== (raw_value = /*quote*/ ctx[0].html + "")) h3.innerHTML = raw_value;			if (dirty & /*attribution*/ 2) set_data(t1, /*attribution*/ ctx[1]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { quote } = $$props;
	let { attribution } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(2, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(3, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(5, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(6, preview_image = $$props.preview_image);
		if ('quote' in $$props) $$invalidate(0, quote = $$props.quote);
		if ('attribution' in $$props) $$invalidate(1, attribution = $$props.attribution);
	};

	return [quote, attribution, color1, color2, favicon, title, preview_image];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$8, safe_not_equal, {
			color1: 2,
			color2: 3,
			favicon: 4,
			title: 5,
			preview_image: 6,
			quote: 0,
			attribution: 1
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$9(ctx) {
	let div;
	let iframe;
	let iframe_src_value;

	return {
		c() {
			div = element("div");
			iframe = element("iframe");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);

			iframe = claim_element(div_nodes, "IFRAME", {
				id: true,
				title: true,
				src: true,
				width: true,
				height: true,
				style: true,
				class: true
			});

			children(iframe).forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(iframe, "id", "take-action");
			attr(iframe, "title", "Take Action");
			if (!src_url_equal(iframe.src, iframe_src_value = "https://gte-form.vercel.app/")) attr(iframe, "src", iframe_src_value);
			attr(iframe, "width", "100%");
			attr(iframe, "height", "1060px");
			set_style(iframe, "border", "0px");
			set_style(iframe, "overflow", "hidden");
			set_style(iframe, "margin", "auto");
			attr(iframe, "class", "svelte-1o7w9hc");
			attr(div, "class", "section");
			attr(div, "id", "section-e4d6227e");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, iframe);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function instance$8($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(0, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(1, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(4, preview_image = $$props.preview_image);
	};

	return [color1, color2, favicon, title, preview_image];
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$8, create_fragment$9, safe_not_equal, {
			color1: 0,
			color2: 1,
			favicon: 2,
			title: 3,
			preview_image: 4
		});
	}
}

/* generated by Svelte v3.58.0 */

function instance$9($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(0, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(1, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(4, preview_image = $$props.preview_image);
	};

	return [color1, color2, favicon, title, preview_image];
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$9, null, safe_not_equal, {
			color1: 0,
			color2: 1,
			favicon: 2,
			title: 3,
			preview_image: 4
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$a(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let t6;
	let component_7;
	let t7;
	let component_8;
	let t8;
	let component_9;
	let current;

	component_0 = new Component({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Edmonton's pro-housing movement.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning Bylaw Renewal - What it is and why it matters",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"size": null
				}
			}
		});

	component_1 = new Component$2({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Edmonton's pro-housing movement.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning Bylaw Renewal - What it is and why it matters",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"size": null
				},
				logo: {
					"image": {
						"alt": "",
						"src": "\thttps://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
						"url": "\thttps://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
						"size": null
					},
					"title": "Grow Together Edmonton"
				},
				site_nav: [
					{
						"link": {
							"url": "/",
							"label": "Home",
							"active": false
						}
					},
					{
						"link": { "url": "/about", "label": "About Us" }
					},
					{
						"link": { "url": "/blog", "label": "News" }
					},
					{
						"link": {
							"url": "/#take-action",
							"label": "Get Involved"
						}
					}
				],
				logo_width: "100"
			}
		});

	component_2 = new Component$3({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Edmonton's pro-housing movement.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning Bylaw Renewal - What it is and why it matters",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"size": null
				},
				content: {
					"html": "<h1>Zoning Bylaw Renewal: What it is and why it matters</h1><p>The City of Edmonton is in the midst of rewriting its Zoning Bylaw.</p><p>It’s a huge undertaking, but the Zoning Bylaw Renewal process is the most powerful tool we have for building the city we need to be in the 21st century.</p><h3>What is Zoning?</h3><p>The zoning bylaw is the set of regulations guiding land-use in the City. Zoning sets out what types of uses and what types of development are expected and permitted in a given area. In simple terms, it’s what prevents oil refineries from going up next to schools. In the real world, zoning has often been used as a tool to segregate communities, restrict more diverse housing options, and build communities without amenities or public transportation.</p><p>Over time, the decisions we make about how to regulate land-use have significant impacts on social inclusion, public health and safety, <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link\" href=\"https://www.gtyeg.ca/affordability\">affordability</a>, <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link\" href=\"https://www.gtyeg.ca/finances\">access to public services, infrastructure demands</a>, transportation, economic development and <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link\" href=\"https://www.gtyeg.ca/climate\">environmental impact</a>.</p>",
					"markdown": "# Zoning Bylaw Renewal: What it is and why it matters\n\nThe City of Edmonton is in the midst of rewriting its Zoning Bylaw.\n\nIt’s a huge undertaking, but the Zoning Bylaw Renewal process is the most powerful tool we have for building the city we need to be in the 21st century.\n\n### What is Zoning?\n\nThe zoning bylaw is the set of regulations guiding land-use in the City. Zoning sets out what types of uses and what types of development are expected and permitted in a given area. In simple terms, it’s what prevents oil refineries from going up next to schools. In the real world, zoning has often been used as a tool to segregate communities, restrict more diverse housing options, and build communities without amenities or public transportation.\n\nOver time, the decisions we make about how to regulate land-use have significant impacts on social inclusion, public health and safety, [affordability](<https://www.gtyeg.ca/affordability>), [access to public services, infrastructure demands](<https://www.gtyeg.ca/finances>), transportation, economic development and [environmental impact](<https://www.gtyeg.ca/climate>).\n\n"
				}
			}
		});

	component_3 = new Component$4({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Edmonton's pro-housing movement.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning Bylaw Renewal - What it is and why it matters",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"size": null
				},
				image: {
					"alt": "Edmonton Zoning Map, 1968",
					"src": "https://dpfecbhwrshlsbfgbgzq.supabase.co/storage/v1/object/public/images/2c45c57d-3334-49f6-bc6a-7fecf6135bc0/1692391129886oldzones1.jpeg",
					"url": "https://dpfecbhwrshlsbfgbgzq.supabase.co/storage/v1/object/public/images/2c45c57d-3334-49f6-bc6a-7fecf6135bc0/1692391129886oldzones1.jpeg",
					"size": 628
				},
				max_height: "400",
				caption: { "html": "", "markdown": "" }
			}
		});

	component_4 = new Component$5({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Edmonton's pro-housing movement.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning Bylaw Renewal - What it is and why it matters",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"size": null
				},
				content: {
					"html": "<h3>Why should I care about zoning?</h3><p>Do you want a grocery store in your neighbourhood? Do you want the local coffee shop to stay in business? Your local school to stay open? Your public services to be high quality? Your taxes to be reasonable? Maybe you’d like to build a suite for a parent or child on your property. Or you’d like to be able to take a quick and efficient bus to work.</p><p>All of these hopes depend on land-use policy and zoning. The way our communities are designed — to bring people together, or keep them apart — is dependent on how we use our land.</p><h3>Why is Edmonton creating a brand new zoning bylaw?</h3><p>Our current zoning bylaw was first drafted in the 1960s, meaning its fundamental structure is still tied to a vision of Edmonton from over 50 years ago. Our population, demographics, land-area, economics and technology have all changed dramatically in that time. The challenges we face as a City, provincially, nationally and globally are also dramatically different.</p><p>At this point, Edmonton’s zoning bylaw is cumbersome, difficult to navigate and understand, and often in conflict with itself. The most innovative, forward-thinking development in our City, often runs contrary to the regulations. Some small businesses need to go through rezoning simply to open their doors, without any changes to the building. This often makes it prohibitive to build more diverse and affordable housing, more complete communities, new local businesses, and needed neighbourhood amenities. Our zoning bylaw does not reflect the goals of our City Plan, the values of our communities, or the practical realities of a diverse and growing ciity.</p><p>Land-use policy is the single most powerful tool that our City has to create a more economically, socially, and environmentally sustainable place. It is essential that this set of tools is relevant to our current context, and adaptable to a rapidly changing world. The new zoning bylaw sets the groundwork for incremental, but more strategic, generational change.</p>",
					"markdown": "### Why should I care about zoning?\n\nDo you want a grocery store in your neighbourhood? Do you want the local coffee shop to stay in business? Your local school to stay open? Your public services to be high quality? Your taxes to be reasonable? Maybe you’d like to build a suite for a parent or child on your property. Or you’d like to be able to take a quick and efficient bus to work.\n\nAll of these hopes depend on land-use policy and zoning. The way our communities are designed — to bring people together, or keep them apart — is dependent on how we use our land.\n\n### Why is Edmonton creating a brand new zoning bylaw?\n\nOur current zoning bylaw was first drafted in the 1960s, meaning its fundamental structure is still tied to a vision of Edmonton from over 50 years ago. Our population, demographics, land-area, economics and technology have all changed dramatically in that time. The challenges we face as a City, provincially, nationally and globally are also dramatically different.\n\nAt this point, Edmonton’s zoning bylaw is cumbersome, difficult to navigate and understand, and often in conflict with itself. The most innovative, forward-thinking development in our City, often runs contrary to the regulations. Some small businesses need to go through rezoning simply to open their doors, without any changes to the building. This often makes it prohibitive to build more diverse and affordable housing, more complete communities, new local businesses, and needed neighbourhood amenities. Our zoning bylaw does not reflect the goals of our City Plan, the values of our communities, or the practical realities of a diverse and growing ciity.\n\nLand-use policy is the single most powerful tool that our City has to create a more economically, socially, and environmentally sustainable place. It is essential that this set of tools is relevant to our current context, and adaptable to a rapidly changing world. The new zoning bylaw sets the groundwork for incremental, but more strategic, generational change.\n\n"
				}
			}
		});

	component_5 = new Component$6({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Edmonton's pro-housing movement.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning Bylaw Renewal - What it is and why it matters",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"size": null
				},
				image: {
					"alt": "An Edmonton zoning map from the 1980s",
					"src": "https://dpfecbhwrshlsbfgbgzq.supabase.co/storage/v1/object/public/images/2c45c57d-3334-49f6-bc6a-7fecf6135bc0/1692391173889oldzones2.jpg",
					"url": "https://dpfecbhwrshlsbfgbgzq.supabase.co/storage/v1/object/public/images/2c45c57d-3334-49f6-bc6a-7fecf6135bc0/1692391173889oldzones2.jpg",
					"size": 8794
				},
				max_height: "400",
				caption: { "html": "", "markdown": "" }
			}
		});

	component_6 = new Component$7({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Edmonton's pro-housing movement.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning Bylaw Renewal - What it is and why it matters",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"size": null
				},
				content: {
					"html": "<h3>What will these changes actually look like?</h3><p>It’s hard to summarize in a few sentences: your experience of the new bylaws will depend a lot on what sort of neighbourhood you live in. But generally speaking, buildings will be allowed to be a little bit taller and a little bit closer together. Mixed-use developments, where businesses are allowed to be below or beside residences, will be a bit more common.</p><p>For a broad overview, the City of Edmonton has an explanation of the new zones and some of the key ways the new bylaw is different on its <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link\" href=\"https://www.google.com/url?q=https://pub-edmonton.escribemeetings.com/filestream.ashx?DocumentId%3D168554&amp;sa=D&amp;source=docs&amp;ust=1692394265754806&amp;usg=AOvVaw0Z033bL3sTuB23IGJ9yEAn\">website</a>. They also offer a <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link\" href=\"https://gis.edmonton.ca/portal/apps/instant/lookup/index.html?appalias=KnowYourZone&amp;appid=e62a2ae63b4141958ffa44b82da09ee9&amp;id=e62a2ae63b4141958ffa44b82da09ee9\">tool</a> to help you figure out which zones will apply to your neighbourhood. Councillors <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link\" href=\"https://www.ashleysalvador.com/post/revamping-the-rulebook-zoning-bylaw-renewal\">Ashley Salvador</a> and <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link\" href=\"https://www.erinrutherford.ca/updates-blog/zoningbylawrenewalvideoandlinks\">Erin Rutherford</a> have also put together deeper considerations of what zoning might mean for their constituents.</p><p>An important thing to remember, though, is that these changes are evolutionary, not revolutionary. Though they’re a necessary step toward building the city we want, that will be a long and slow process.</p>",
					"markdown": "### What will these changes actually look like?\n\nIt’s hard to summarize in a few sentences: your experience of the new bylaws will depend a lot on what sort of neighbourhood you live in. But generally speaking, buildings will be allowed to be a little bit taller and a little bit closer together. Mixed-use developments, where businesses are allowed to be below or beside residences, will be a bit more common.\n\nFor a broad overview, the City of Edmonton has an explanation of the new zones and some of the key ways the new bylaw is different on its [website](<https://www.google.com/url?q=https://pub-edmonton.escribemeetings.com/filestream.ashx?DocumentId%3D168554&sa=D&source=docs&ust=1692394265754806&usg=AOvVaw0Z033bL3sTuB23IGJ9yEAn>). They also offer a [tool](<https://gis.edmonton.ca/portal/apps/instant/lookup/index.html?appalias=KnowYourZone&appid=e62a2ae63b4141958ffa44b82da09ee9&id=e62a2ae63b4141958ffa44b82da09ee9>) to help you figure out which zones will apply to your neighbourhood. Councillors [Ashley Salvador](<https://www.ashleysalvador.com/post/revamping-the-rulebook-zoning-bylaw-renewal>) and [Erin Rutherford](<https://www.erinrutherford.ca/updates-blog/zoningbylawrenewalvideoandlinks>) have also put together deeper considerations of what zoning might mean for their constituents.\n\nAn important thing to remember, though, is that these changes are evolutionary, not revolutionary. Though they’re a necessary step toward building the city we want, that will be a long and slow process.\n\n"
				}
			}
		});

	component_7 = new Component$8({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Edmonton's pro-housing movement.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning Bylaw Renewal - What it is and why it matters",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"size": null
				},
				quote: {
					"html": "<h3>We have to build the future we want.</h3><p></p><h3><a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link link\" href=\"https://www.gtyeg.ca/#take-action\">Get involved</a> and help create an Edmonton that’s sustainable, affordable and vibrant for everyone.</h3>",
					"markdown": "### We have to build the future we want.\n\n\n\n### [Get involved](<https://www.gtyeg.ca/#take-action>) and help create an Edmonton that’s sustainable, affordable and vibrant for everyone.\n\n"
				},
				attribution: ""
			}
		});

	component_8 = new Component$9({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Edmonton's pro-housing movement.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning Bylaw Renewal - What it is and why it matters",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"size": null
				}
			}
		});

	component_9 = new Component$a({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Edmonton's pro-housing movement.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning Bylaw Renewal - What it is and why it matters",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692640844/Grow_Together_Edmonton_LOGO_B4_y7r6qd.png",
					"size": null
				}
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
			t6 = space();
			create_component(component_7.$$.fragment);
			t7 = space();
			create_component(component_8.$$.fragment);
			t8 = space();
			create_component(component_9.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
			t6 = claim_space(nodes);
			claim_component(component_7.$$.fragment, nodes);
			t7 = claim_space(nodes);
			claim_component(component_8.$$.fragment, nodes);
			t8 = claim_space(nodes);
			claim_component(component_9.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			insert_hydration(target, t6, anchor);
			mount_component(component_7, target, anchor);
			insert_hydration(target, t7, anchor);
			mount_component(component_8, target, anchor);
			insert_hydration(target, t8, anchor);
			mount_component(component_9, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			transition_in(component_7.$$.fragment, local);
			transition_in(component_8.$$.fragment, local);
			transition_in(component_9.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			transition_out(component_7.$$.fragment, local);
			transition_out(component_8.$$.fragment, local);
			transition_out(component_9.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
			if (detaching) detach(t6);
			destroy_component(component_7, detaching);
			if (detaching) detach(t7);
			destroy_component(component_8, detaching);
			if (detaching) detach(t8);
			destroy_component(component_9, detaching);
		}
	};
}

class Component$b extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$a, safe_not_equal, {});
	}
}

export default Component$b;
