+++
title = 'Is Digital Cash Perfect for Micromobility?'
date = 2024-07-22T19:19:21-07:00
+++

My first real job was to write code for a company which helped clients plan outdoor advertising campaigns. I guess it isn't hard to acquire semi-anonymized trip data, because we had lots. After entering demographic information like age, gender, and purchase behavior for your desired audience, our app would display a street heatmap of where that audience most frequently traveled. All that was left to do was rent some billboards and bus ads along those streets, design some art, and boom: an apparently highly effective ad campaign.

That was in 2019, when micromobility products like Lime and Nike Biketown were beginning to take off. Nowadays they're much more popular, and it actually looks like they're going to stay in our cities. While I don't know for sure, it would be surprising if these enterprising vendors weren't selling trips data.

> After removing certain identifiers, such as your name, phone, and e-mail address (where provided), and combining the resulting information with similar information from other users, Lime may share your information, including individual trip records and trip location (journey) history, with third parties for research, business or other purposes.
>
> [Lime Privacy Policy](https://www.li.me/legal/privacy-policy) (accessed July 22nd, 2024)

![A Nike Biketown receipt](biketown.jpeg#right)

Micromobility supply is more volatile than public transit. Buses run on fixed schedules and rarely fill up completely. On the other hand, an in-use Lime scooter cannot be used another person. Moreover, micromobility is often used for short distances, and only if it is convenient. In other words, if you walk out of a bar and see a Lime scooter 50ft away, you might be tempted to actually use it. If not, then you might just walk or call a Lyft. This opportunity cost of an in-use product is why micromobility vendors charge a a minutely fee in addition to an unlock fee, whereas a monthly bus pass typically costs a fixed amount. While you can sometimes buy a monthly subscription to a micromobility service, for most that just waives the unlock fees. For the typical ride, these minutely fees don't add up to be much---maybe just a few dollars. This is all to explain why, [even though users apparently despise them](https://web.archive.org/web/20040612004748/http://shirky.com/writings/fame_vs_fortune.html), micropayments are somewhat intrinsic to micromobility.

An ordinary bus pass allows the transit company to learn where you boarded, but not where you disembarked. It's also practical to accept cash or coins on a bus, which renders any cryptographic anonymity solution less necessary. This is not true for micromobility devices. Also, [for loss-prevention reasons](https://www.wweek.com/culture/2018/08/13/someone-started-a-website-to-track-how-many-e-scooters-end-up-in-the-willamette-river/), GPS chips are integrated into micromobility devices. Even if you disable tracking on your phone, it is easy for the vendor to tie your entire trip to your identity.

For these reasons, I suggest that micromobility vendors should adopt a form of digital cash like [GNU Taler](https://taler.net/en/index.html). It might look like this: when you sign up for the service, you get a few free unlocks and 30 minutes of riding (both could be implemented as anonymous digital cash). Like a pay-as-you-go phone, you can reload your minutes in the app. Convenience stores could even sell scratch-off codes for users that want to pay with cash, which is especially sensical since [there are many low-income and homeless micromobility users](https://biketownpdx.com/pricing/biketown-for-all) who may not have a bank account.


[Unlike ride-sharing](https://eprint.iacr.org/2024/1109.pdf), micromobility is inherently centralized. There is a company that needs to be responsible for distributing, recharging, and repairing the devices. Users are already placing a tremendous amount of trust in the vendor by assuming that, for instance, [the brakes work properly](https://www.consumerreports.org/product-safety/brake-problems-in-lime-electric-scooters-causing-accidents-and-injuries/). With this in mind, it is not unreasonable to trust the vendor to honor the riding time tokens you purchased. There is certainly no need for cryptocurrency here, which would just complicate things further.

While this hypothetical e-cash micromobility system would no longer allow vendors to make money from selling demographic-linked trips data, avoiding micropayments might actually save them some money. In a world where users are hungry for privacy and every scooter looks the same as every other scooter, anonymity could be a differentiating selling point.
But more importantly than these monetary incentivers, preserving user privacy is the right thing to do. I'm not so deluded to think that vendors would adopt an untracable payment system on their own accord, but perhaps local legislation could be drafted which mandates the use of untracable e-cash for micromobility.

One issue with this anonymous transit system: how will vendors ban users who misbehave? Preventing users from leaving scooters in sidewalks, locking their bikes up to parking meters, or just straight-up vandalizing devices is a serious concern for these companies. Thankfully cryptographers have already thought about this issue, and revocable anonymity is somewhat well-studied. One solution would empower a judge or city official with the ability to issue information to the micromobility provider which allows them to learn the credit card details of the last few users of a specific device (like a search warrant). Another idea could be to require a user to show their real ID to a city official in order to obtain a pseudonym to use with the vendor, with the idea that the vendor can provide evidence for a misbehaving pseudonym, after which point the city can just stop issuing pseudonyms for that user if they're found guilty, or even prosecute them. In any case, micromobility vandalism doesn't seem to be *that* big of an issue: [Lime reported that only 1% of their U.S. scooters were vandalized in 2018](https://www.forbes.com/sites/johnfrazer1/2019/02/07/how-were-solving-the-shared-scooter-theft-problem/). Granted, anonymous users might be more likely to misbehave.

Digital cash didn't take off in the 90's, for both [technical](https://www.forbes.com/forbes/1999/1101/6411390a.html) and [non-technical](https://web.archive.org/web/20130204131817/https://cryptome.org/jya/digicrash.htm) reasons. While large-scale adoption of digital cash seems impossible at this point, it still a genius idea that remains practical for many applications. Small steps like this idea could serve a blow to data brokers and predatory advertising companies whose targeted ads [can deepen inequality](https://www.bbc.com/worklife/article/20200817-the-inequality-of-outdoor-advertising-exposure).

### Notes

[There's a Multibillion-Dollar Market for Your Phone's Location Data](https://themarkup.org/privacy/2021/09/30/theres-a-multibillion-dollar-market-for-your-phones-location-data)

More evidence for the fact that some micromobility users don't have a bank account:

> We provide prepaid debit cards for those who do not have a bank account, or do not feel comfortable inputting their bank information into the BIKETOWN app.
> 
> [Biketown Prepaid Debit Cards](https://www.portland.gov/transportation/bike-share/about-biketown), accessed July 22nd, 2024.

[Anonymous Credentials](https://eprint.iacr.org/2001/019.pdf)

Stadler, M., Piveteau, JM., Camenisch, J. Fair Blind Signatures. EUROCRYPT ’95. [https://doi.org/10.1007/3-540-49264-X\_17](https://doi.org/10.1007/3-540-49264-X\_17)

Obligatory [Blind Signatures for Untraceable Payments](https://sceweb.sce.uhcl.edu/yang/teaching/csci5234WebSecurityFall2011/Chaum-blind-signatures.PDF)
