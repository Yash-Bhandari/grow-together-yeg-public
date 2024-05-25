// Get Involved - Updated May 25, 2024
function noop() { }
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
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
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
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
function insert(target, node, anchor) {
    target.insertBefore(node, anchor || null);
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
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
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
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
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
function find_comment(nodes, text, start) {
    for (let i = start; i < nodes.length; i += 1) {
        const node = nodes[i];
        if (node.nodeType === 8 /* comment node */ && node.textContent.trim() === text) {
            return i;
        }
    }
    return nodes.length;
}
function claim_html_tag(nodes, is_svg) {
    // find html opening tag
    const start_index = find_comment(nodes, 'HTML_TAG_START', 0);
    const end_index = find_comment(nodes, 'HTML_TAG_END', start_index);
    if (start_index === end_index) {
        return new HtmlTagHydration(undefined, is_svg);
    }
    init_claim_info(nodes);
    const html_tag_nodes = nodes.splice(start_index, end_index - start_index + 1);
    detach(html_tag_nodes[0]);
    detach(html_tag_nodes[html_tag_nodes.length - 1]);
    const claimed_nodes = html_tag_nodes.slice(1, html_tag_nodes.length - 1);
    for (const n of claimed_nodes) {
        n.claim_order = nodes.claim_info.total_claimed;
        nodes.claim_info.total_claimed += 1;
    }
    return new HtmlTagHydration(claimed_nodes, is_svg);
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
class HtmlTag {
    constructor(is_svg = false) {
        this.is_svg = false;
        this.is_svg = is_svg;
        this.e = this.n = null;
    }
    c(html) {
        this.h(html);
    }
    m(html, target, anchor = null) {
        if (!this.e) {
            if (this.is_svg)
                this.e = svg_element(target.nodeName);
            /** #7364  target for <template> may be provided as #document-fragment(11) */
            else
                this.e = element((target.nodeType === 11 ? 'TEMPLATE' : target.nodeName));
            this.t = target.tagName !== 'TEMPLATE' ? target : target.content;
            this.c(html);
        }
        this.i(anchor);
    }
    h(html) {
        this.e.innerHTML = html;
        this.n = Array.from(this.e.nodeName === 'TEMPLATE' ? this.e.content.childNodes : this.e.childNodes);
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert(this.t, this.n[i], anchor);
        }
    }
    p(html) {
        this.d();
        this.h(html);
        this.i(this.a);
    }
    d() {
        this.n.forEach(detach);
    }
}
class HtmlTagHydration extends HtmlTag {
    constructor(claimed_nodes, is_svg = false) {
        super(is_svg);
        this.e = this.n = null;
        this.l = claimed_nodes;
    }
    c(html) {
        if (this.l) {
            this.n = this.l;
        }
        else {
            super.c(html);
        }
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert_hydration(this.t, this.n[i], anchor);
        }
    }
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
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

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
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

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      // Allow provider without '@': "provider:prefix:name"
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};

const defaultIconDimensions = Object.freeze(
  {
    left: 0,
    top: 0,
    width: 16,
    height: 16
  }
);
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});

function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}

function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}

function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}

function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(
      icons[name2] || aliases[name2],
      currentProps
    );
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}

function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}

const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(
      icon,
      defaultExtendedIconProps
    )) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(
      icon,
      defaultExtendedIconProps
    )) {
      return null;
    }
  }
  return data;
}

const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage.icons[name] = icon;
    } else {
      storage.missing.add(name);
    }
  });
}
function addIconToStorage(storage, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage.icons[name] = { ...icon };
      return true;
    }
  } catch (err) {
  }
  return false;
}

let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage.icons[iconName] || (storage.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage = getStorage(provider, prefix);
  return !!addIconSet(storage, data);
}

const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  // Dimensions
  ...defaultIconSizeCustomisations,
  // Transformations
  ...defaultIconTransformations
});

const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}

function splitSVGDefs(content, tag = "defs") {
  let defs = "";
  const index = content.indexOf("<" + tag);
  while (index >= 0) {
    const start = content.indexOf(">", index);
    const end = content.indexOf("</" + tag);
    if (start === -1 || end === -1) {
      break;
    }
    const endEnd = content.indexOf(">", end);
    if (endEnd === -1) {
      break;
    }
    defs += content.slice(start + 1, end).trim();
    content = content.slice(0, index).trim() + content.slice(endEnd + 1);
  }
  return {
    defs,
    content
  };
}
function mergeDefsAndContent(defs, content) {
  return defs ? "<defs>" + defs + "</defs>" + content : content;
}
function wrapSVGContent(body, start, end) {
  const split = splitSVGDefs(body);
  return mergeDefsAndContent(split.defs, start + split.content + end);
}

const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push(
          "translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")"
        );
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push(
        "translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")"
      );
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift(
          "rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")"
        );
        break;
      case 2:
        transformations.unshift(
          "rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")"
        );
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift(
          "rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")"
        );
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = wrapSVGContent(
        body,
        '<g transform="' + transformations.join(" ") + '">',
        "</g>"
      );
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  const viewBox = [box.left, box.top, boxWidth, boxHeight];
  attributes.viewBox = viewBox.join(" ");
  return {
    attributes,
    viewBox,
    body
  };
}

const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(
      // Allowed characters before id: [#;"]
      // Allowed characters after id: [)"], .[a-z]
      new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"),
      "$1" + newID + suffix + "$3"
    );
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}

const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}

function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    // API hosts
    resources,
    // Root path
    path: source.path || "/",
    // URL length limit
    maxURL: source.maxURL || 500,
    // Timeout before next host is used.
    rotate: source.rotate || 750,
    // Timeout before failing query.
    timeout: source.timeout || 5e3,
    // Randomise default API end point.
    random: source.random === true,
    // Start index
    index: source.index || 0,
    // Receive data after time out (used if time out kicks in first, then API module sends data anyway).
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}

const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};

function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage[provider] || (storage[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}

function removeCallback(storages, id) {
  storages.forEach((storage) => {
    const items = storage.loaderCallbacks;
    if (items) {
      storage.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage) {
  if (!storage.pendingCallbacksFlag) {
    storage.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage.pendingCallbacksFlag = false;
      const items = storage.loaderCallbacks ? storage.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage.provider;
      const prefix = storage.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage], item.id);
          }
          item.callback(
            icons.loaded.slice(0),
            icons.missing.slice(0),
            icons.pending.slice(0),
            item.abort
          );
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage) => {
    (storage.loaderCallbacks || (storage.loaderCallbacks = [])).push(item);
  });
  return abort;
}

function listToIcons(list, validate = true, simpleNames = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}

// src/config.ts
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};

// src/query.ts
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}

// src/index.ts
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(
      config,
      payload,
      queryCallback,
      (data, error) => {
        cleanup();
        if (doneCallback) {
          doneCallback(data, error);
        }
      }
    );
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}

function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send = api.send;
      }
    }
  }
  if (!redundancy || !send) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send, callback)().abort;
}

const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
const browserStorageLimit = 50;

function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}

function setBrowserStorageItemsCount(storage, value) {
  return setStoredItem(storage, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage) {
  return parseInt(getStoredItem(storage, browserCacheCountKey)) || 0;
}

const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}

let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}

function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && // Valid item: run callback
      callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}

function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage = getStorage(
        provider,
        prefix
      );
      if (!addIconSet(storage, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage.lastModifiedCached = storage.lastModifiedCached ? Math.min(storage.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}

function updateLastModified(storage, lastModified) {
  const lastValue = storage.lastModifiedCached;
  if (
    // Matches or newer
    lastValue && lastValue >= lastModified
  ) {
    return lastValue === lastModified;
  }
  storage.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage.provider || iconSet.prefix !== storage.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (index >= browserStorageLimit || !setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage.provider,
      data
    };
    return setStoredItem(
      func,
      browserCachePrefix + index.toString(),
      JSON.stringify(item)
    );
  }
  if (data.lastModified && !updateLastModified(storage, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}

function emptyCallback() {
}
function loadedNewIcons(storage) {
  if (!storage.iconsLoaderFlag) {
    storage.iconsLoaderFlag = true;
    setTimeout(() => {
      storage.iconsLoaderFlag = false;
      updateCallbacks(storage);
    });
  }
}
function loadNewIcons(storage, icons) {
  if (!storage.iconsToLoad) {
    storage.iconsToLoad = icons;
  } else {
    storage.iconsToLoad = storage.iconsToLoad.concat(icons).sort();
  }
  if (!storage.iconsQueueFlag) {
    storage.iconsQueueFlag = true;
    setTimeout(() => {
      storage.iconsQueueFlag = false;
      const { provider, prefix } = storage;
      const icons2 = storage.iconsToLoad;
      delete storage.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(
                storage,
                data
              );
              if (!parsed.length) {
                return;
              }
              const pending = storage.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(
            sortedIcons.loaded,
            sortedIcons.missing,
            sortedIcons.pending,
            emptyCallback
          );
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const { provider, prefix } = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const { provider, prefix, name } = icon;
    const storage = getStorage(provider, prefix);
    const pendingQueue = storage.pendingIcons || (storage.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage) => {
    const { provider, prefix } = storage;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};

function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}

const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}

function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}

function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}

function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}

const defaultExtendedIconCustomisations = {
    ...defaultIconCustomisations,
    inline: false,
};

/**
 * Default SVG attributes
 */
const svgDefaults = {
    'xmlns': 'http://www.w3.org/2000/svg',
    'xmlns:xlink': 'http://www.w3.org/1999/xlink',
    'aria-hidden': true,
    'role': 'img',
};
/**
 * Style modes
 */
const commonProps = {
    display: 'inline-block',
};
const monotoneProps = {
    'background-color': 'currentColor',
};
const coloredProps = {
    'background-color': 'transparent',
};
// Dynamically add common props to variables above
const propsToAdd = {
    image: 'var(--svg)',
    repeat: 'no-repeat',
    size: '100% 100%',
};
const propsToAddTo = {
    '-webkit-mask': monotoneProps,
    'mask': monotoneProps,
    'background': coloredProps,
};
for (const prefix in propsToAddTo) {
    const list = propsToAddTo[prefix];
    for (const prop in propsToAdd) {
        list[prefix + '-' + prop] = propsToAdd[prop];
    }
}
/**
 * Fix size: add 'px' to numbers
 */
function fixSize(value) {
    return value + (value.match(/^[-0-9.]+$/) ? 'px' : '');
}
/**
 * Generate icon from properties
 */
function render(
// Icon must be validated before calling this function
icon, 
// Properties
props) {
    const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
    // Check mode
    const mode = props.mode || 'svg';
    const componentProps = (mode === 'svg' ? { ...svgDefaults } : {});
    if (icon.body.indexOf('xlink:') === -1) {
        delete componentProps['xmlns:xlink'];
    }
    // Create style if missing
    let style = typeof props.style === 'string' ? props.style : '';
    // Get element properties
    for (let key in props) {
        const value = props[key];
        if (value === void 0) {
            continue;
        }
        switch (key) {
            // Properties to ignore
            case 'icon':
            case 'style':
            case 'onLoad':
            case 'mode':
                break;
            // Boolean attributes
            case 'inline':
            case 'hFlip':
            case 'vFlip':
                customisations[key] =
                    value === true || value === 'true' || value === 1;
                break;
            // Flip as string: 'horizontal,vertical'
            case 'flip':
                if (typeof value === 'string') {
                    flipFromString(customisations, value);
                }
                break;
            // Color: copy to style, add extra ';' in case style is missing it
            case 'color':
                style =
                    style +
                        (style.length > 0 && style.trim().slice(-1) !== ';'
                            ? ';'
                            : '') +
                        'color: ' +
                        value +
                        '; ';
                break;
            // Rotation as string
            case 'rotate':
                if (typeof value === 'string') {
                    customisations[key] = rotateFromString(value);
                }
                else if (typeof value === 'number') {
                    customisations[key] = value;
                }
                break;
            // Remove aria-hidden
            case 'ariaHidden':
            case 'aria-hidden':
                if (value !== true && value !== 'true') {
                    delete componentProps['aria-hidden'];
                }
                break;
            default:
                if (key.slice(0, 3) === 'on:') {
                    // Svelte event
                    break;
                }
                // Copy missing property if it does not exist in customisations
                if (defaultExtendedIconCustomisations[key] === void 0) {
                    componentProps[key] = value;
                }
        }
    }
    // Generate icon
    const item = iconToSVG(icon, customisations);
    const renderAttribs = item.attributes;
    // Inline display
    if (customisations.inline) {
        // Style overrides it
        style = 'vertical-align: -0.125em; ' + style;
    }
    if (mode === 'svg') {
        // Add icon stuff
        Object.assign(componentProps, renderAttribs);
        // Style
        if (style !== '') {
            componentProps.style = style;
        }
        // Counter for ids based on "id" property to render icons consistently on server and client
        let localCounter = 0;
        let id = props.id;
        if (typeof id === 'string') {
            // Convert '-' to '_' to avoid errors in animations
            id = id.replace(/-/g, '_');
        }
        // Generate HTML
        return {
            svg: true,
            attributes: componentProps,
            body: replaceIDs(item.body, id ? () => id + 'ID' + localCounter++ : 'iconifySvelte'),
        };
    }
    // Render <span> with style
    const { body, width, height } = icon;
    const useMask = mode === 'mask' ||
        (mode === 'bg' ? false : body.indexOf('currentColor') !== -1);
    // Generate SVG
    const html = iconToHTML(body, {
        ...renderAttribs,
        width: width + '',
        height: height + '',
    });
    // Generate style
    const url = svgToURL(html);
    const styles = {
        '--svg': url,
    };
    const size = (prop) => {
        const value = renderAttribs[prop];
        if (value) {
            styles[prop] = fixSize(value);
        }
    };
    size('width');
    size('height');
    Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
    let customStyle = '';
    for (const key in styles) {
        customStyle += key + ': ' + styles[key] + ';';
    }
    componentProps.style = customStyle + style;
    return {
        svg: false,
        attributes: componentProps,
    };
}
/**
 * Initialise stuff
 */
// Enable short names
allowSimpleNames(true);
// Set API module
setAPIModule('', fetchAPIModule);
/**
 * Browser stuff
 */
if (typeof document !== 'undefined' && typeof window !== 'undefined') {
    // Set cache and load existing cache
    initBrowserStorage();
    const _window = window;
    // Load icons from global "IconifyPreload"
    if (_window.IconifyPreload !== void 0) {
        const preload = _window.IconifyPreload;
        const err = 'Invalid IconifyPreload syntax.';
        if (typeof preload === 'object' && preload !== null) {
            (preload instanceof Array ? preload : [preload]).forEach((item) => {
                try {
                    if (
                    // Check if item is an object and not null/array
                    typeof item !== 'object' ||
                        item === null ||
                        item instanceof Array ||
                        // Check for 'icons' and 'prefix'
                        typeof item.icons !== 'object' ||
                        typeof item.prefix !== 'string' ||
                        // Add icon set
                        !addCollection(item)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            });
        }
    }
    // Set API from global "IconifyProviders"
    if (_window.IconifyProviders !== void 0) {
        const providers = _window.IconifyProviders;
        if (typeof providers === 'object' && providers !== null) {
            for (let key in providers) {
                const err = 'IconifyProviders[' + key + '] is invalid.';
                try {
                    const value = providers[key];
                    if (typeof value !== 'object' ||
                        !value ||
                        value.resources === void 0) {
                        continue;
                    }
                    if (!addAPIProvider(key, value)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            }
        }
    }
}
/**
 * Check if component needs to be updated
 */
function checkIconState(icon, state, mounted, callback, onload) {
    // Abort loading icon
    function abortLoading() {
        if (state.loading) {
            state.loading.abort();
            state.loading = null;
        }
    }
    // Icon is an object
    if (typeof icon === 'object' &&
        icon !== null &&
        typeof icon.body === 'string') {
        // Stop loading
        state.name = '';
        abortLoading();
        return { data: { ...defaultIconProps, ...icon } };
    }
    // Invalid icon?
    let iconName;
    if (typeof icon !== 'string' ||
        (iconName = stringToIcon(icon, false, true)) === null) {
        abortLoading();
        return null;
    }
    // Load icon
    const data = getIconData(iconName);
    if (!data) {
        // Icon data is not available
        // Do not load icon until component is mounted
        if (mounted && (!state.loading || state.loading.name !== icon)) {
            // New icon to load
            abortLoading();
            state.name = '';
            state.loading = {
                name: icon,
                abort: loadIcons([iconName], callback),
            };
        }
        return null;
    }
    // Icon data is available
    abortLoading();
    if (state.name !== icon) {
        state.name = icon;
        if (onload && !state.destroyed) {
            onload(icon);
        }
    }
    // Add classes
    const classes = ['iconify'];
    if (iconName.prefix !== '') {
        classes.push('iconify--' + iconName.prefix);
    }
    if (iconName.provider !== '') {
        classes.push('iconify--' + iconName.provider);
    }
    return { data, classes };
}
/**
 * Generate icon
 */
function generateIcon(icon, props) {
    return icon
        ? render({
            ...defaultIconProps,
            ...icon,
        }, props)
        : null;
}

/* generated by Svelte v3.59.1 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (115:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (111:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		{
			const iconData = checkIconState($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

let Component$1 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i];
	return child_ctx;
}

// (86:4) {#each socials as social}
function create_each_block(ctx) {
	let a;
	let icon;
	let t0;
	let t1_value = /*social*/ ctx[3].link.label + "";
	let t1;
	let t2;
	let a_href_value;
	let current;
	icon = new Component$1({ props: { icon: /*social*/ ctx[3].icon } });

	return {
		c() {
			a = element("a");
			create_component(icon.$$.fragment);
			t0 = space();
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			t0 = claim_space(a_nodes);
			t1 = claim_text(a_nodes, t1_value);
			t2 = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*social*/ ctx[3].link.url);
			attr(a, "class", "svelte-7ai3jx");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			mount_component(icon, a, null);
			append_hydration(a, t0);
			append_hydration(a, t1);
			append_hydration(a, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*socials*/ 2) icon_changes.icon = /*social*/ ctx[3].icon;
			icon.$set(icon_changes);
			if ((!current || dirty & /*socials*/ 2) && t1_value !== (t1_value = /*social*/ ctx[3].link.label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*socials*/ 2 && a_href_value !== (a_href_value = /*social*/ ctx[3].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

function create_fragment(ctx) {
	let section;
	let div0;
	let h2;
	let t0;
	let div1;
	let t1;
	let div3;
	let html_tag;
	let raw1_value = /*subheading*/ ctx[2].html + "";
	let t2;
	let div2;
	let t3;
	let style0;
	let t4;
	let t5;
	let style1;
	let t6;
	let t7;
	let div15;
	let div14;
	let div13;
	let div10;
	let div4;
	let h40;
	let t8;
	let t9;
	let p0;
	let t10;
	let t11;
	let form;
	let div7;
	let div6;
	let div5;
	let label;
	let t12;
	let t13;
	let input0;
	let t14;
	let input1;
	let t15;
	let div9;
	let button0;
	let t16;
	let t17;
	let button1;
	let div8;
	let t18;
	let span;
	let t19;
	let t20;
	let input2;
	let t21;
	let div12;
	let div11;
	let h41;
	let t22;
	let t23;
	let p1;
	let t24;
	let t25;
	let script0;
	let t26;
	let t27;
	let script1;
	let script1_src_value;
	let t28;
	let script2;
	let t29;
	let current;
	let each_value = /*socials*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			section = element("section");
			div0 = element("div");
			h2 = element("h2");
			t0 = space();
			div1 = element("div");
			t1 = space();
			div3 = element("div");
			html_tag = new HtmlTagHydration(false);
			t2 = space();
			div2 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t3 = space();
			style0 = element("style");
			t4 = text("@import url(\"https://assets.mlcdn.com/fonts.css?version=1689246\");");
			t5 = space();
			style1 = element("style");
			t6 = text("/* LOADER */\n    .ml-form-embedSubmitLoad {\n      display: inline-block;\n      width: 20px;\n      height: 20px;\n    }\n\n    .g-recaptcha {\n    transform: scale(1);\n    -webkit-transform: scale(1);\n    transform-origin: 0 0;\n    -webkit-transform-origin: 0 0;\n    height: ;\n    }\n\n    .sr-only {\n      position: absolute;\n      width: 1px;\n      height: 1px;\n      padding: 0;\n      margin: -1px;\n      overflow: hidden;\n      clip: rect(0,0,0,0);\n      border: 0;\n    }\n\n    .ml-form-embedSubmitLoad:after {\n      content: \" \";\n      display: block;\n      width: 11px;\n      height: 11px;\n      margin: 1px;\n      border-radius: 50%;\n      border: 4px solid #fff;\n    border-color: #ffffff #ffffff #ffffff transparent;\n    animation: ml-form-embedSubmitLoad 1.2s linear infinite;\n    }\n    @keyframes ml-form-embedSubmitLoad {\n      0% {\n      transform: rotate(0deg);\n      }\n      100% {\n      transform: rotate(360deg);\n      }\n    }\n      #mlb2-6312828.ml-form-embedContainer {\n        box-sizing: border-box;\n        display: table;\n        margin: 0 auto;\n        position: static;\n        width: 100% !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer h4,\n      #mlb2-6312828.ml-form-embedContainer p,\n      #mlb2-6312828.ml-form-embedContainer span,\n      #mlb2-6312828.ml-form-embedContainer button {\n        text-transform: none !important;\n        letter-spacing: normal !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper {\n        background-color: #f6f6f6;\n        \n        border-width: 0px;\n        border-color: transparent;\n        border-radius: 4px;\n        border-style: solid;\n        box-sizing: border-box;\n        display: inline-block !important;\n        margin: 0;\n        padding: 0;\n        position: relative;\n              }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedPopup,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedDefault { width: 400px; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedForm { max-width: 400px; width: 100%; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-left { text-align: left; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-center { text-align: center; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-default { display: table-cell !important; vertical-align: middle !important; text-align: center !important; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-right { text-align: right; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedHeader img {\n        border-top-left-radius: 4px;\n        border-top-right-radius: 4px;\n        height: auto;\n        margin: 0 auto !important;\n        max-width: 100%;\n        width: undefinedpx;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody {\n        padding: 20px 20px 0 20px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody.ml-form-embedBodyHorizontal {\n        padding-bottom: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent {\n        text-align: left;\n        margin: 0 0 20px 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent h4,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent h4 {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 30px;\n        font-weight: 400;\n        margin: 0 0 10px 0;\n        text-align: left;\n        word-break: break-word;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n        font-weight: 400;\n        line-height: 20px;\n        margin: 0 0 10px 0;\n        text-align: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ul,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ul,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol ol {\n        list-style-type: lower-alpha;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol ol ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol ol ol {\n        list-style-type: lower-roman;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p a,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p a {\n        color: #000000;\n        text-decoration: underline;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-block-form .ml-field-group {\n        text-align: left!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-block-form .ml-field-group label {\n        margin-bottom: 5px;\n        color: #333333;\n        font-size: 14px;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-weight: bold; font-style: normal; text-decoration: none;;\n        display: inline-block;\n        line-height: 20px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p:last-child,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p:last-child {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody form {\n        margin: 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-formContent,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow {\n        margin: 0 0 20px 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow {\n        float: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-formContent.horozintalForm {\n        margin: 0;\n        padding: 0 0 20px 0;\n        width: 100%;\n        height: auto;\n        float: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow {\n        margin: 0 0 10px 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow.ml-last-item {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow.ml-formfieldHorizintal {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        height: auto;\n        line-height: 21px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        margin-left: 0;\n        margin-right: 0;\n        padding: 10px 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input::-webkit-input-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input::-webkit-input-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input::-moz-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input::-moz-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input:-ms-input-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input:-ms-input-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input:-moz-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input:-moz-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow textarea, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow textarea {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        height: auto;\n        line-height: 21px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n          border-color: #cccccc!important;\n          background-color: #ffffff!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input.custom-control-input[type=\"checkbox\"]{\n        box-sizing: border-box;\n        padding: 0;\n        position: absolute;\n        z-index: -1;\n        opacity: 0;\n        margin-top: 5px;\n        margin-left: -1.5rem;\n        overflow: visible;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n        border-radius: 4px!important;\n      }\n\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=checkbox]:checked~.label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox input[type=checkbox]:checked~.label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox input[type=checkbox]:checked~.label-description::after {\n        background-image: url(\"data:image/svg+xml,%3csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 8 8'%3e%3cpath fill='%23fff' d='M6.564.75l-3.59 3.612-1.538-1.55L0 4.26 2.974 7.25 8 2.193z'/%3e%3c/svg%3e\");\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::after {\n        background-image: url(\"data:image/svg+xml,%3csvg xmlns='http://www.w3.org/2000/svg' viewBox='-4 -4 8 8'%3e%3ccircle r='3' fill='%23fff'/%3e%3c/svg%3e\");\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox input[type=checkbox]:checked~.label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox input[type=checkbox]:checked~.label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=checkbox]:checked~.label-description::before  {\n          border-color: #000000!important;\n          background-color: #000000!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::after {\n           top: 2px;\n           box-sizing: border-box;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n           top: 0px!important;\n           box-sizing: border-box!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n        top: 0px!important;\n           box-sizing: border-box!important;\n      }\n\n       #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::after {\n            top: 0px!important;\n            box-sizing: border-box!important;\n            position: absolute;\n            left: -1.5rem;\n            display: block;\n            width: 1rem;\n            height: 1rem;\n            content: \"\";\n       }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before {\n        top: 0px!important;\n        box-sizing: border-box!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-control-label::before {\n          position: absolute;\n          top: 4px;\n          left: -1.5rem;\n          display: block;\n          width: 16px;\n          height: 16px;\n          pointer-events: none;\n          content: \"\";\n          background-color: #ffffff;\n          border: #adb5bd solid 1px;\n          border-radius: 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-control-label::after {\n          position: absolute;\n          top: 2px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n          position: absolute;\n          top: 4px;\n          left: -1.5rem;\n          display: block;\n          width: 16px;\n          height: 16px;\n          pointer-events: none;\n          content: \"\";\n          background-color: #ffffff;\n          border: #adb5bd solid 1px;\n          border-radius: 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after {\n          position: absolute;\n          top: 0px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n          position: absolute;\n          top: 0px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-radio .custom-control-label::after {\n          background: no-repeat 50%/50% 50%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-checkbox .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n          background: no-repeat 50%/50% 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-control, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-control {\n        position: relative;\n        display: block;\n        min-height: 1.5rem;\n        padding-left: 1.5rem;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input {\n          position: absolute;\n          z-index: -1;\n          opacity: 0;\n          box-sizing: border-box;\n          padding: 0;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label {\n          color: #000000;\n          font-size: 12px!important;\n          font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n          line-height: 22px;\n          margin-bottom: 0;\n          position: relative;\n          vertical-align: top;\n          font-style: normal;\n          font-weight: 700;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-select, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-select {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        line-height: 20px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 28px 10px 12px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n        height: auto;\n        display: inline-block;\n        vertical-align: middle;\n        background: url('https://assets.mlcdn.com/ml/images/default/dropdown.svg') no-repeat right .75rem center/8px 10px;\n        -webkit-appearance: none;\n        -moz-appearance: none;\n        appearance: none;\n      }\n\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow {\n        height: auto;\n        width: 100%;\n        float: left;\n      }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal { width: 70%; float: left; }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-button-horizontal { width: 30%; float: left; }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-button-horizontal.labelsOn { padding-top: 25px;  }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .horizontal-fields { box-sizing: border-box; float: left; padding-right: 10px;  }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input {\n        background-color: #ffffff;\n        color: #333333;\n        border-color: #cccccc;\n        border-radius: 4px;\n        border-style: solid;\n        border-width: 1px;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n        line-height: 20px;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 10px;\n        width: 100%;\n        box-sizing: border-box;\n        overflow-y: initial;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow button {\n        background-color: #004700 !important;\n        border-color: #004700;\n        border-style: solid;\n        border-width: 1px;\n        border-radius: 4px;\n        box-shadow: none;\n        color: #ffffff !important;\n        cursor: pointer;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        font-weight: 700;\n        line-height: 20px;\n        margin: 0 !important;\n        padding: 10px !important;\n        width: 100%;\n        height: auto;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow button:hover {\n        background-color: #333333 !important;\n        border-color: #333333 !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=\"checkbox\"] {\n        box-sizing: border-box;\n        padding: 0;\n        position: absolute;\n        z-index: -1;\n        opacity: 0;\n        margin-top: 5px;\n        margin-left: -1.5rem;\n        overflow: visible;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description {\n        color: #000000;\n        display: block;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 12px;\n        text-align: left;\n        margin-bottom: 0;\n        position: relative;\n        vertical-align: top;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label {\n        font-weight: normal;\n        margin: 0;\n        padding: 0;\n        position: relative;\n        display: block;\n        min-height: 24px;\n        padding-left: 24px;\n\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label a {\n        color: #000000;\n        text-decoration: underline;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label p {\n        color: #000000 !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif !important;\n        font-size: 12px !important;\n        font-weight: normal !important;\n        line-height: 18px !important;\n        padding: 0 !important;\n        margin: 0 5px 0 0 !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label p:last-child {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit {\n        margin: 0 0 20px 0;\n        float: left;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button {\n        background-color: #027648 !important;\n        border: none !important;\n        border-radius: 4px !important;\n        box-shadow: none !important;\n        color: #ffffff !important;\n        cursor: pointer;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif !important;\n        font-size: 14px !important;\n        font-weight: 700 !important;\n        line-height: 21px !important;\n        height: auto;\n        padding: 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button.loading {\n        display: none;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button:hover {\n        background-color: #333333 !important;\n      }\n      .ml-subscribe-close {\n        width: 30px;\n        height: 30px;\n        background: url('https://assets.mlcdn.com/ml/images/default/modal_close.png') no-repeat;\n        background-size: 30px;\n        cursor: pointer;\n        margin-top: -10px;\n        margin-right: -10px;\n        position: absolute;\n        top: 0;\n        right: 0;\n      }\n      .ml-error input, .ml-error textarea, .ml-error select {\n        border-color: red!important;\n      }\n\n      .ml-error .custom-checkbox-radio-list {\n        border: 1px solid red !important;\n        border-radius: 4px;\n        padding: 10px;\n      }\n\n      .ml-error .label-description,\n      .ml-error .label-description p,\n      .ml-error .label-description p a,\n      .ml-error label:first-child {\n        color: #ff0000 !important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow.ml-error .label-description p,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow.ml-error .label-description p:first-letter {\n        color: #ff0000 !important;\n      }\n            @media only screen and (max-width: 400px){\n\n        .ml-form-embedWrapper.embedDefault, .ml-form-embedWrapper.embedPopup { width: 100%!important; }\n        .ml-form-formContent.horozintalForm { float: left!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow { height: auto!important; width: 100%!important; float: left!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal { width: 100%!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal > div { padding-right: 0px!important; padding-bottom: 10px; }\n        .ml-form-formContent.horozintalForm .ml-button-horizontal { width: 100%!important; }\n        .ml-form-formContent.horozintalForm .ml-button-horizontal.labelsOn { padding-top: 0px!important; }\n\n      }");
			t7 = space();
			div15 = element("div");
			div14 = element("div");
			div13 = element("div");
			div10 = element("div");
			div4 = element("div");
			h40 = element("h4");
			t8 = text("Newsletter");
			t9 = space();
			p0 = element("p");
			t10 = text("Join our mailing list for updates and events.");
			t11 = space();
			form = element("form");
			div7 = element("div");
			div6 = element("div");
			div5 = element("div");
			label = element("label");
			t12 = text("Email");
			t13 = space();
			input0 = element("input");
			t14 = space();
			input1 = element("input");
			t15 = space();
			div9 = element("div");
			button0 = element("button");
			t16 = text("Subscribe");
			t17 = space();
			button1 = element("button");
			div8 = element("div");
			t18 = space();
			span = element("span");
			t19 = text("Loading...");
			t20 = space();
			input2 = element("input");
			t21 = space();
			div12 = element("div");
			div11 = element("div");
			h41 = element("h4");
			t22 = text("Thank you!");
			t23 = space();
			p1 = element("p");
			t24 = text("You have successfully joined our subscriber list.");
			t25 = space();
			script0 = element("script");
			t26 = text("function ml_webform_success_6312828() {\n      var $ = ml_jQuery || jQuery;\n      $('.ml-subscribe-form-6312828 .row-success').show();\n      $('.ml-subscribe-form-6312828 .row-form').hide();\n    }");
			t27 = space();
			script1 = element("script");
			t28 = space();
			script2 = element("script");
			t29 = text("fetch(\"https://assets.mailerlite.com/jsonp/511328/forms/93691462163629222/track-view\")");
			this.h();
		},
		l(nodes) {
			section = claim_element(nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", {});
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			h2_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t0 = claim_space(section_nodes);
			div1 = claim_element(section_nodes, "DIV", {});
			children(div1).forEach(detach);
			t1 = claim_space(section_nodes);
			div3 = claim_element(section_nodes, "DIV", { class: true, style: true });
			var div3_nodes = children(div3);
			html_tag = claim_html_tag(div3_nodes, false);
			t2 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div2_nodes);
			}

			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			style0 = claim_element(section_nodes, "STYLE", { type: true });
			var style0_nodes = children(style0);
			t4 = claim_text(style0_nodes, "@import url(\"https://assets.mlcdn.com/fonts.css?version=1689246\");");
			style0_nodes.forEach(detach);
			t5 = claim_space(section_nodes);
			style1 = claim_element(section_nodes, "STYLE", { type: true });
			var style1_nodes = children(style1);
			t6 = claim_text(style1_nodes, "/* LOADER */\n    .ml-form-embedSubmitLoad {\n      display: inline-block;\n      width: 20px;\n      height: 20px;\n    }\n\n    .g-recaptcha {\n    transform: scale(1);\n    -webkit-transform: scale(1);\n    transform-origin: 0 0;\n    -webkit-transform-origin: 0 0;\n    height: ;\n    }\n\n    .sr-only {\n      position: absolute;\n      width: 1px;\n      height: 1px;\n      padding: 0;\n      margin: -1px;\n      overflow: hidden;\n      clip: rect(0,0,0,0);\n      border: 0;\n    }\n\n    .ml-form-embedSubmitLoad:after {\n      content: \" \";\n      display: block;\n      width: 11px;\n      height: 11px;\n      margin: 1px;\n      border-radius: 50%;\n      border: 4px solid #fff;\n    border-color: #ffffff #ffffff #ffffff transparent;\n    animation: ml-form-embedSubmitLoad 1.2s linear infinite;\n    }\n    @keyframes ml-form-embedSubmitLoad {\n      0% {\n      transform: rotate(0deg);\n      }\n      100% {\n      transform: rotate(360deg);\n      }\n    }\n      #mlb2-6312828.ml-form-embedContainer {\n        box-sizing: border-box;\n        display: table;\n        margin: 0 auto;\n        position: static;\n        width: 100% !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer h4,\n      #mlb2-6312828.ml-form-embedContainer p,\n      #mlb2-6312828.ml-form-embedContainer span,\n      #mlb2-6312828.ml-form-embedContainer button {\n        text-transform: none !important;\n        letter-spacing: normal !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper {\n        background-color: #f6f6f6;\n        \n        border-width: 0px;\n        border-color: transparent;\n        border-radius: 4px;\n        border-style: solid;\n        box-sizing: border-box;\n        display: inline-block !important;\n        margin: 0;\n        padding: 0;\n        position: relative;\n              }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedPopup,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedDefault { width: 400px; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedForm { max-width: 400px; width: 100%; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-left { text-align: left; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-center { text-align: center; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-default { display: table-cell !important; vertical-align: middle !important; text-align: center !important; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-right { text-align: right; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedHeader img {\n        border-top-left-radius: 4px;\n        border-top-right-radius: 4px;\n        height: auto;\n        margin: 0 auto !important;\n        max-width: 100%;\n        width: undefinedpx;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody {\n        padding: 20px 20px 0 20px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody.ml-form-embedBodyHorizontal {\n        padding-bottom: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent {\n        text-align: left;\n        margin: 0 0 20px 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent h4,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent h4 {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 30px;\n        font-weight: 400;\n        margin: 0 0 10px 0;\n        text-align: left;\n        word-break: break-word;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n        font-weight: 400;\n        line-height: 20px;\n        margin: 0 0 10px 0;\n        text-align: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ul,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ul,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol ol {\n        list-style-type: lower-alpha;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol ol ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol ol ol {\n        list-style-type: lower-roman;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p a,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p a {\n        color: #000000;\n        text-decoration: underline;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-block-form .ml-field-group {\n        text-align: left!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-block-form .ml-field-group label {\n        margin-bottom: 5px;\n        color: #333333;\n        font-size: 14px;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-weight: bold; font-style: normal; text-decoration: none;;\n        display: inline-block;\n        line-height: 20px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p:last-child,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p:last-child {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody form {\n        margin: 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-formContent,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow {\n        margin: 0 0 20px 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow {\n        float: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-formContent.horozintalForm {\n        margin: 0;\n        padding: 0 0 20px 0;\n        width: 100%;\n        height: auto;\n        float: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow {\n        margin: 0 0 10px 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow.ml-last-item {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow.ml-formfieldHorizintal {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        height: auto;\n        line-height: 21px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        margin-left: 0;\n        margin-right: 0;\n        padding: 10px 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input::-webkit-input-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input::-webkit-input-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input::-moz-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input::-moz-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input:-ms-input-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input:-ms-input-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input:-moz-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input:-moz-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow textarea, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow textarea {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        height: auto;\n        line-height: 21px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n          border-color: #cccccc!important;\n          background-color: #ffffff!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input.custom-control-input[type=\"checkbox\"]{\n        box-sizing: border-box;\n        padding: 0;\n        position: absolute;\n        z-index: -1;\n        opacity: 0;\n        margin-top: 5px;\n        margin-left: -1.5rem;\n        overflow: visible;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n        border-radius: 4px!important;\n      }\n\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=checkbox]:checked~.label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox input[type=checkbox]:checked~.label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox input[type=checkbox]:checked~.label-description::after {\n        background-image: url(\"data:image/svg+xml,%3csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 8 8'%3e%3cpath fill='%23fff' d='M6.564.75l-3.59 3.612-1.538-1.55L0 4.26 2.974 7.25 8 2.193z'/%3e%3c/svg%3e\");\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::after {\n        background-image: url(\"data:image/svg+xml,%3csvg xmlns='http://www.w3.org/2000/svg' viewBox='-4 -4 8 8'%3e%3ccircle r='3' fill='%23fff'/%3e%3c/svg%3e\");\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox input[type=checkbox]:checked~.label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox input[type=checkbox]:checked~.label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=checkbox]:checked~.label-description::before  {\n          border-color: #000000!important;\n          background-color: #000000!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::after {\n           top: 2px;\n           box-sizing: border-box;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n           top: 0px!important;\n           box-sizing: border-box!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n        top: 0px!important;\n           box-sizing: border-box!important;\n      }\n\n       #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::after {\n            top: 0px!important;\n            box-sizing: border-box!important;\n            position: absolute;\n            left: -1.5rem;\n            display: block;\n            width: 1rem;\n            height: 1rem;\n            content: \"\";\n       }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before {\n        top: 0px!important;\n        box-sizing: border-box!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-control-label::before {\n          position: absolute;\n          top: 4px;\n          left: -1.5rem;\n          display: block;\n          width: 16px;\n          height: 16px;\n          pointer-events: none;\n          content: \"\";\n          background-color: #ffffff;\n          border: #adb5bd solid 1px;\n          border-radius: 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-control-label::after {\n          position: absolute;\n          top: 2px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n          position: absolute;\n          top: 4px;\n          left: -1.5rem;\n          display: block;\n          width: 16px;\n          height: 16px;\n          pointer-events: none;\n          content: \"\";\n          background-color: #ffffff;\n          border: #adb5bd solid 1px;\n          border-radius: 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after {\n          position: absolute;\n          top: 0px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n          position: absolute;\n          top: 0px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-radio .custom-control-label::after {\n          background: no-repeat 50%/50% 50%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-checkbox .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n          background: no-repeat 50%/50% 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-control, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-control {\n        position: relative;\n        display: block;\n        min-height: 1.5rem;\n        padding-left: 1.5rem;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input {\n          position: absolute;\n          z-index: -1;\n          opacity: 0;\n          box-sizing: border-box;\n          padding: 0;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label {\n          color: #000000;\n          font-size: 12px!important;\n          font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n          line-height: 22px;\n          margin-bottom: 0;\n          position: relative;\n          vertical-align: top;\n          font-style: normal;\n          font-weight: 700;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-select, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-select {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        line-height: 20px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 28px 10px 12px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n        height: auto;\n        display: inline-block;\n        vertical-align: middle;\n        background: url('https://assets.mlcdn.com/ml/images/default/dropdown.svg') no-repeat right .75rem center/8px 10px;\n        -webkit-appearance: none;\n        -moz-appearance: none;\n        appearance: none;\n      }\n\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow {\n        height: auto;\n        width: 100%;\n        float: left;\n      }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal { width: 70%; float: left; }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-button-horizontal { width: 30%; float: left; }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-button-horizontal.labelsOn { padding-top: 25px;  }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .horizontal-fields { box-sizing: border-box; float: left; padding-right: 10px;  }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input {\n        background-color: #ffffff;\n        color: #333333;\n        border-color: #cccccc;\n        border-radius: 4px;\n        border-style: solid;\n        border-width: 1px;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n        line-height: 20px;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 10px;\n        width: 100%;\n        box-sizing: border-box;\n        overflow-y: initial;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow button {\n        background-color: #004700 !important;\n        border-color: #004700;\n        border-style: solid;\n        border-width: 1px;\n        border-radius: 4px;\n        box-shadow: none;\n        color: #ffffff !important;\n        cursor: pointer;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        font-weight: 700;\n        line-height: 20px;\n        margin: 0 !important;\n        padding: 10px !important;\n        width: 100%;\n        height: auto;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow button:hover {\n        background-color: #333333 !important;\n        border-color: #333333 !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=\"checkbox\"] {\n        box-sizing: border-box;\n        padding: 0;\n        position: absolute;\n        z-index: -1;\n        opacity: 0;\n        margin-top: 5px;\n        margin-left: -1.5rem;\n        overflow: visible;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description {\n        color: #000000;\n        display: block;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 12px;\n        text-align: left;\n        margin-bottom: 0;\n        position: relative;\n        vertical-align: top;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label {\n        font-weight: normal;\n        margin: 0;\n        padding: 0;\n        position: relative;\n        display: block;\n        min-height: 24px;\n        padding-left: 24px;\n\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label a {\n        color: #000000;\n        text-decoration: underline;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label p {\n        color: #000000 !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif !important;\n        font-size: 12px !important;\n        font-weight: normal !important;\n        line-height: 18px !important;\n        padding: 0 !important;\n        margin: 0 5px 0 0 !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label p:last-child {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit {\n        margin: 0 0 20px 0;\n        float: left;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button {\n        background-color: #027648 !important;\n        border: none !important;\n        border-radius: 4px !important;\n        box-shadow: none !important;\n        color: #ffffff !important;\n        cursor: pointer;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif !important;\n        font-size: 14px !important;\n        font-weight: 700 !important;\n        line-height: 21px !important;\n        height: auto;\n        padding: 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button.loading {\n        display: none;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button:hover {\n        background-color: #333333 !important;\n      }\n      .ml-subscribe-close {\n        width: 30px;\n        height: 30px;\n        background: url('https://assets.mlcdn.com/ml/images/default/modal_close.png') no-repeat;\n        background-size: 30px;\n        cursor: pointer;\n        margin-top: -10px;\n        margin-right: -10px;\n        position: absolute;\n        top: 0;\n        right: 0;\n      }\n      .ml-error input, .ml-error textarea, .ml-error select {\n        border-color: red!important;\n      }\n\n      .ml-error .custom-checkbox-radio-list {\n        border: 1px solid red !important;\n        border-radius: 4px;\n        padding: 10px;\n      }\n\n      .ml-error .label-description,\n      .ml-error .label-description p,\n      .ml-error .label-description p a,\n      .ml-error label:first-child {\n        color: #ff0000 !important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow.ml-error .label-description p,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow.ml-error .label-description p:first-letter {\n        color: #ff0000 !important;\n      }\n            @media only screen and (max-width: 400px){\n\n        .ml-form-embedWrapper.embedDefault, .ml-form-embedWrapper.embedPopup { width: 100%!important; }\n        .ml-form-formContent.horozintalForm { float: left!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow { height: auto!important; width: 100%!important; float: left!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal { width: 100%!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal > div { padding-right: 0px!important; padding-bottom: 10px; }\n        .ml-form-formContent.horozintalForm .ml-button-horizontal { width: 100%!important; }\n        .ml-form-formContent.horozintalForm .ml-button-horizontal.labelsOn { padding-top: 0px!important; }\n\n      }");
			style1_nodes.forEach(detach);
			t7 = claim_space(section_nodes);
			div15 = claim_element(section_nodes, "DIV", { id: true, class: true });
			var div15_nodes = children(div15);
			div14 = claim_element(div15_nodes, "DIV", { class: true });
			var div14_nodes = children(div14);
			div13 = claim_element(div14_nodes, "DIV", { class: true });
			var div13_nodes = children(div13);
			div10 = claim_element(div13_nodes, "DIV", { class: true });
			var div10_nodes = children(div10);
			div4 = claim_element(div10_nodes, "DIV", { class: true, style: true });
			var div4_nodes = children(div4);
			h40 = claim_element(div4_nodes, "H4", {});
			var h40_nodes = children(h40);
			t8 = claim_text(h40_nodes, "Newsletter");
			h40_nodes.forEach(detach);
			t9 = claim_space(div4_nodes);
			p0 = claim_element(div4_nodes, "P", {});
			var p0_nodes = children(p0);
			t10 = claim_text(p0_nodes, "Join our mailing list for updates and events.");
			p0_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			t11 = claim_space(div10_nodes);

			form = claim_element(div10_nodes, "FORM", {
				class: true,
				action: true,
				"data-code": true,
				method: true,
				target: true
			});

			var form_nodes = children(form);
			div7 = claim_element(form_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			label = claim_element(div5_nodes, "LABEL", { for: true });
			var label_nodes = children(label);
			t12 = claim_text(label_nodes, "Email");
			label_nodes.forEach(detach);
			t13 = claim_space(div5_nodes);

			input0 = claim_element(div5_nodes, "INPUT", {
				id: true,
				"aria-label": true,
				"aria-required": true,
				type: true,
				class: true,
				"data-inputmask": true,
				name: true,
				placeholder: true,
				autocomplete: true
			});

			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			t14 = claim_space(form_nodes);
			input1 = claim_element(form_nodes, "INPUT", { type: true, name: true });
			t15 = claim_space(form_nodes);
			div9 = claim_element(form_nodes, "DIV", { class: true });
			var div9_nodes = children(div9);
			button0 = claim_element(div9_nodes, "BUTTON", { type: true, class: true });
			var button0_nodes = children(button0);
			t16 = claim_text(button0_nodes, "Subscribe");
			button0_nodes.forEach(detach);
			t17 = claim_space(div9_nodes);
			button1 = claim_element(div9_nodes, "BUTTON", { style: true, type: true, class: true });
			var button1_nodes = children(button1);
			div8 = claim_element(button1_nodes, "DIV", { class: true });
			children(div8).forEach(detach);
			t18 = claim_space(button1_nodes);
			span = claim_element(button1_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t19 = claim_text(span_nodes, "Loading...");
			span_nodes.forEach(detach);
			button1_nodes.forEach(detach);
			div9_nodes.forEach(detach);
			t20 = claim_space(form_nodes);
			input2 = claim_element(form_nodes, "INPUT", { type: true, name: true });
			form_nodes.forEach(detach);
			div10_nodes.forEach(detach);
			t21 = claim_space(div13_nodes);
			div12 = claim_element(div13_nodes, "DIV", { class: true, style: true });
			var div12_nodes = children(div12);
			div11 = claim_element(div12_nodes, "DIV", { class: true });
			var div11_nodes = children(div11);
			h41 = claim_element(div11_nodes, "H4", {});
			var h41_nodes = children(h41);
			t22 = claim_text(h41_nodes, "Thank you!");
			h41_nodes.forEach(detach);
			t23 = claim_space(div11_nodes);
			p1 = claim_element(div11_nodes, "P", {});
			var p1_nodes = children(p1);
			t24 = claim_text(p1_nodes, "You have successfully joined our subscriber list.");
			p1_nodes.forEach(detach);
			div11_nodes.forEach(detach);
			div12_nodes.forEach(detach);
			div13_nodes.forEach(detach);
			div14_nodes.forEach(detach);
			div15_nodes.forEach(detach);
			t25 = claim_space(section_nodes);
			script0 = claim_element(section_nodes, "SCRIPT", {});
			var script0_nodes = children(script0);
			t26 = claim_text(script0_nodes, "function ml_webform_success_6312828() {\n      var $ = ml_jQuery || jQuery;\n      $('.ml-subscribe-form-6312828 .row-success').show();\n      $('.ml-subscribe-form-6312828 .row-form').hide();\n    }");
			script0_nodes.forEach(detach);
			t27 = claim_space(section_nodes);
			script1 = claim_element(section_nodes, "SCRIPT", { src: true, type: true });
			var script1_nodes = children(script1);
			script1_nodes.forEach(detach);
			t28 = claim_space(section_nodes);
			script2 = claim_element(section_nodes, "SCRIPT", {});
			var script2_nodes = children(script2);
			t29 = claim_text(script2_nodes, "fetch(\"https://assets.mailerlite.com/jsonp/511328/forms/93691462163629222/track-view\")");
			script2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading");
			html_tag.a = t2;
			attr(div2, "class", "social-links svelte-7ai3jx");
			attr(div3, "class", "content svelte-7ai3jx");
			attr(div3, "style", "body");
			attr(style0, "type", "text/css");
			attr(style1, "type", "text/css");
			attr(div4, "class", "ml-form-embedContent");
			attr(div4, "style", "");
			attr(label, "for", "subscribe-to-list");
			attr(input0, "id", "subscribe-to-list");
			attr(input0, "aria-label", "email");
			attr(input0, "aria-required", "true");
			attr(input0, "type", "email");
			attr(input0, "class", "form-control");
			attr(input0, "data-inputmask", "");
			attr(input0, "name", "fields[email]");
			attr(input0, "placeholder", "");
			attr(input0, "autocomplete", "email");
			attr(div5, "class", "ml-field-group ml-field-email ml-validate-email ml-validate-required");
			attr(div6, "class", "ml-form-fieldRow ml-last-item");
			attr(div7, "class", "ml-form-formContent");
			attr(input1, "type", "hidden");
			attr(input1, "name", "ml-submit");
			input1.value = "1";
			attr(button0, "type", "submit");
			attr(button0, "class", "primary");
			attr(div8, "class", "ml-form-embedSubmitLoad");
			attr(span, "class", "sr-only");
			button1.disabled = "disabled";
			set_style(button1, "display", "none");
			attr(button1, "type", "button");
			attr(button1, "class", "loading");
			attr(div9, "class", "ml-form-embedSubmit");
			attr(input2, "type", "hidden");
			attr(input2, "name", "anticsrf");
			input2.value = "true";
			attr(form, "class", "ml-block-form");
			attr(form, "action", "https://assets.mailerlite.com/jsonp/511328/forms/93691462163629222/subscribe");
			attr(form, "data-code", "");
			attr(form, "method", "post");
			attr(form, "target", "_blank");
			attr(div10, "class", "ml-form-embedBody ml-form-embedBodyDefault row-form");
			attr(div11, "class", "ml-form-successContent");
			attr(div12, "class", "ml-form-successBody row-success");
			set_style(div12, "display", "none");
			attr(div13, "class", "ml-form-embedWrapper embedForm");
			attr(div14, "class", "ml-form-align-center ");
			attr(div15, "id", "mlb2-6312828");
			attr(div15, "class", "ml-form-embedContainer ml-subscribe-form ml-subscribe-form-6312828");
			if (!src_url_equal(script1.src, script1_src_value = "https://groot.mailerlite.com/js/w/webforms.min.js?vc2affd81117220f6978e779b988d5128")) attr(script1, "src", script1_src_value);
			attr(script1, "type", "text/javascript");
			attr(section, "class", "section-container svelte-7ai3jx");
		},
		m(target, anchor) {
			insert_hydration(target, section, anchor);
			append_hydration(section, div0);
			append_hydration(div0, h2);
			h2.innerHTML = /*heading*/ ctx[0];
			append_hydration(section, t0);
			append_hydration(section, div1);
			append_hydration(section, t1);
			append_hydration(section, div3);
			html_tag.m(raw1_value, div3);
			append_hydration(div3, t2);
			append_hydration(div3, div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div2, null);
				}
			}

			append_hydration(section, t3);
			append_hydration(section, style0);
			append_hydration(style0, t4);
			append_hydration(section, t5);
			append_hydration(section, style1);
			append_hydration(style1, t6);
			append_hydration(section, t7);
			append_hydration(section, div15);
			append_hydration(div15, div14);
			append_hydration(div14, div13);
			append_hydration(div13, div10);
			append_hydration(div10, div4);
			append_hydration(div4, h40);
			append_hydration(h40, t8);
			append_hydration(div4, t9);
			append_hydration(div4, p0);
			append_hydration(p0, t10);
			append_hydration(div10, t11);
			append_hydration(div10, form);
			append_hydration(form, div7);
			append_hydration(div7, div6);
			append_hydration(div6, div5);
			append_hydration(div5, label);
			append_hydration(label, t12);
			append_hydration(div5, t13);
			append_hydration(div5, input0);
			append_hydration(form, t14);
			append_hydration(form, input1);
			append_hydration(form, t15);
			append_hydration(form, div9);
			append_hydration(div9, button0);
			append_hydration(button0, t16);
			append_hydration(div9, t17);
			append_hydration(div9, button1);
			append_hydration(button1, div8);
			append_hydration(button1, t18);
			append_hydration(button1, span);
			append_hydration(span, t19);
			append_hydration(form, t20);
			append_hydration(form, input2);
			append_hydration(div13, t21);
			append_hydration(div13, div12);
			append_hydration(div12, div11);
			append_hydration(div11, h41);
			append_hydration(h41, t22);
			append_hydration(div11, t23);
			append_hydration(div11, p1);
			append_hydration(p1, t24);
			append_hydration(section, t25);
			append_hydration(section, script0);
			append_hydration(script0, t26);
			append_hydration(section, t27);
			append_hydration(section, script1);
			append_hydration(section, t28);
			append_hydration(section, script2);
			append_hydration(script2, t29);
			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) h2.innerHTML = /*heading*/ ctx[0];			if ((!current || dirty & /*subheading*/ 4) && raw1_value !== (raw1_value = /*subheading*/ ctx[2].html + "")) html_tag.p(raw1_value);

			if (dirty & /*socials*/ 2) {
				each_value = /*socials*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div2, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(section);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let { event } = $$props;
	let { social } = $$props;
	let { heading } = $$props;
	let { socials } = $$props;
	let { subheading } = $$props;

	// Mailerlite
	window.setTimeout(
		() => {
			(function (w, d, e, u, f, l, n) {
				(w[f] = w[f] || function () {
					(w[f].q = w[f].q || []).push(arguments); //ml('account', '511328')
				}, l = d.createElement(e), l.async = 1, l.src = u, n = d.getElementsByTagName(e)[0], n.parentNode.insertBefore(l, n));
			})(window, document, 'script', 'https://assets.mailerlite.com/js/universal.js', 'ml');
		},
		5000
	); //ml('account', '511328')

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(4, props = $$props.props);
		if ('event' in $$props) $$invalidate(5, event = $$props.event);
		if ('social' in $$props) $$invalidate(3, social = $$props.social);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('socials' in $$props) $$invalidate(1, socials = $$props.socials);
		if ('subheading' in $$props) $$invalidate(2, subheading = $$props.subheading);
	};

	return [heading, socials, subheading, social, props, event];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			props: 4,
			event: 5,
			social: 3,
			heading: 0,
			socials: 1,
			subheading: 2
		});
	}
}

export { Component as default };
