const getRandomArbitrary = (min, max) => Math.random() * (max - min) + min;

const getRandomInt = (min, max) => {
    min = Math.ceil(min);
    max = Math.floor(max);
    return Math.floor(Math.random() * (max - min + 1)) + min;
}

let genuine = true;

document.addEventListener('keydown', function (event) {
    if (event.key == 'Control') genuine = false;
});

document.addEventListener('keyup', function (event) {
    genuine = true;
});

const rng = async () => {
    const elRes = document.getElementById("result");
    const elVrfInput = document.getElementById('vrfInput');
    let vrfInput = elVrfInput.value;

    let hashHex = '';
    while (true) {
        const msgBuffer = new TextEncoder().encode(vrfInput);

        // hash the message
        const hashBuffer = await crypto.subtle.digest('SHA-256', msgBuffer);

        // convert ArrayBuffer to Array
        const hashArray = Array.from(new Uint8Array(hashBuffer));

        // convert bytes to hex string                  
        hashHex = hashArray.map(b => b.toString(16).padStart(2, '0')).join('');

        if (!genuine && hashHex[hashHex.length - 1] != '0') {
            vrfInput = vrfInput + 'a';
        } else {
            break;
        }
    }

    elRes.innerHTML = hashHex;
}