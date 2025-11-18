package controller.utente;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Autore;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;
import model.wishList.WishList;

import java.io.IOException;
import java.util.List;

@WebServlet("/mostra-libro")
public class MostraLibroServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

        String isbn=request.getParameter("isbn");
        HttpSession session= request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if(Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            dispatcher.forward(request, response);
        }
        else {
            Carrello carrello = (Carrello) session.getAttribute("carrello");
            WishList wishList = (WishList) session.getAttribute("wishList");
            Libro libro = new Libro();
            LibroDAO libroService = new LibroDAO();
            boolean presenza = false;
            if (carrello != null) {
                for (RigaCarrello riga : carrello.getRigheCarrello()) {
                    Libro libroRiga = riga.getLibro();
                    if (libroRiga.getIsbn().equals(isbn)) {
                        libro = libroRiga;
                        presenza = true;
                        break;
                    }

                }
            } else if (wishList != null) {
                for (Libro libro1 : wishList.getLibri()) {
                    if (libro1.getIsbn().equals(isbn)) {
                        libro = libro1;
                        presenza = true;
                        break;
                    }
                }
            }
            if (!presenza) {
                libro = libroService.doRetrieveById(isbn);
            }

            List<Autore> autori = libroService.getScrittura(isbn);


            request.setAttribute("libro", libro);
            request.setAttribute("autori", autori);

            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/mostraLibro.jsp");
            dispatcher.forward(request, response);
        }
    }
}
