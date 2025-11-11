package controller.utente;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Reparto;
import model.utenteService.Utente;
import model.wishList.WishList;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@WebServlet("/modifica-preferiti")
public class ModificaPrefServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String isbn = request.getParameter("isbn");
        String source=request.getParameter("source");
        String position = request.getParameter("position");

        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");

        String address="index.html";
        LibroDAO libroService = new LibroDAO();
        Libro libro = libroService.doRetrieveById(isbn);

        if(utente==null) {
            address = "/WEB-INF/results/login.jsp";
        }

        else {
            if(source!= null && source.equals("wishList")){// controllo se il bottone è stato selezionato nella show WishList
                address="/WEB-INF/results/showWishList.jsp";
            }
            else if(source!= null && source.equals("reparto")){// controllo se il bottone è stato selezionato nel reparto
                if(request.getParameter("repartoAttuale")!=null) {
                    int idReparto = Integer.parseInt(request.getParameter("repartoAttuale"));
                    List<Reparto> reparti = (List<Reparto>) getServletContext().getAttribute("reparti");
                    for(Reparto r : reparti) {
                        if(r.getIdReparto()==idReparto) {
                            request.setAttribute("reparto", r);
                        }
                    }
                    address = "/WEB-INF/results/reparto.jsp";
                }
            }else if(source!= null && source.equals("mostraLibro")){
                address = "/WEB-INF/results/mostraLibro.jsp";
                request.setAttribute("libro", libro);
            }
            WishList wishList = (WishList) session.getAttribute("wishList");
            boolean flag = true; // libro non presente
            if (wishList != null && wishList.getLibri() != null) {
                for (int i = 0; i < wishList.getLibri().size() && flag; i++) {
                    if (wishList.getLibri().get(i).equals(libro)) {
                        wishList.getLibri().remove(i); // libro già presente, lo rimuovo
                        flag = false;
                    }
                }
                if (flag)// se il libro non è presente, lo aggiungo
                    wishList.getLibri().add(libro);
            } else {
                wishList.setLibri(new ArrayList<model.libroService.Libro>());
                wishList.getLibri().add(libro);
            }
            session.setAttribute("wishList", wishList);

            if (position != null) {
                address += "#" + position;
            }

        }

        RequestDispatcher dispatcher = request.getRequestDispatcher(address);
        dispatcher.forward(request, response);
    }
}
