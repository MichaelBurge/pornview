(function () {
    let mkFuncs = function(funcs) {
        return {
            mkQueryString: function(params) {
                let esc = encodeURIComponent;
                return Object.keys(params)
                             .map(k => esc(k) + '=' + esc(params[k]))
                             .join('&');
            },
            getQueryDict: function() {
                var qd = {};
                if (location.search) {
                    location.search.substr(1).split`&`.forEach(item => {
                        let [k,v] = item.split`=`;
                        v = v && decodeURIComponent(v);
                        (qd[k] = qd[k] || []).push(v)
                    });
                }
                return qd;
            },
            fetchJson: function(uri, options, onFetch) {
                window.fetch(uri, options).then(function(response) {
                    if (! response.ok) {
                        console.log("Error: ", response);
                        return;
                    }
                    response.json().then(onFetch);
                });
            },
            tagImage: function(imageId, cat, onTag) {
                funcs.fetchJson("/api/tagImage/" + imageId + "/" + cat, {method: "POST"}, onTag);
            },
            untagImage: function(imageId, cat, onUntag) {
                funcs.fetchJson("/api/untagImage/" + imageId + "/" + cat, {method: "POST"}, onUntag);
            },
            mkTagButton: function(imageId, cat) {
                let btn = document.createElement("button");
                btn.innerText = "Tag " + cat;
                btn.onclick = () => { funcs.tagImage(imageId, cat); };
                return btn;
            },
            mkUntagButton: function(imageId, cat) {
                let btn = document.createElement("button");
                btn.innerText = "Untag " + cat;
                btn.onclick = () => { funcs.untagImage(imageId, cat); };
                return btn;
            },
            refreshCategories: function() {
                funcs.fetchJson("api/listCategories", {}, data => {
                    let ul = document.getElementById("categories");
                    data.forEach(catName => {
                        let li = document.createElement("li");
                        let a = document.createElement("a");
                        a.innerText = catName;
                        a.href = "/?" + funcs.mkQueryString({ "category": catName });
                        li.appendChild(a);
                        ul.appendChild(li);
                    });
                });
            },
            refreshImages: function() {
                funcs.fetchJson("api/listImages?category=" + (qd["category"] || ""), {}, data => {
                    console.log(qd);
                    let ul = document.getElementById("thumbs");
                    data.forEach(data => {
                        let [ id, filename, _ ] = data;
                        let filenameUri = "images/" + id;
                        let li = document.createElement("li");
                        let a = document.createElement("a");
                        a.href = filenameUri;
                        let img = document.createElement("img");
                        img.src = filenameUri;
                        a.appendChild(img);
                        li.appendChild(a);
                        li.appendChild(funcs.mkTagButton(id, "Catgirls"));
                        li.appendChild(funcs.mkTagButton(id, "Catboys"));
                        li.appendChild(funcs.mkTagButton(id, "Floor Tiles"));
                        li.appendChild(funcs.mkUntagButton(id, "Catgirls"));
                        li.appendChild(funcs.mkUntagButton(id, "Catboys"));
                        li.appendChild(funcs.mkUntagButton(id, "Floor Tiles"));

                        ul.appendChild(li);
                    });
                });
            }
        };
    };
    let funcs;
    funcs = mkFuncs(funcs);
    funcs = mkFuncs(funcs);
    funcs = mkFuncs(funcs);
    funcs = mkFuncs(funcs);
    let qd = funcs.getQueryDict();
    funcs.refreshCategories();
    funcs.refreshImages();

})();
