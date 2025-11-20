package controller.admin.gestisciProdotti;

import model.libroService.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

public class ModificaLibroServletTest {

    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
    }

    /**
     * Test case: Valid ISBN provided, book exists and is properly displayed with all associated data
     */
    @Test
    public void testDoGet_ValidISBN_Success() throws Exception {
        // Arrange
        String isbn = "978-3-16-148410-0";
        
        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setTitolo("Clean Code");
        libro.setGenere("Programming");
        libro.setPrezzo(45.99);
        libro.setSconto(10);

        Sede sede1 = new Sede();
        sede1.setIdSede(1);
        sede1.setCitta("Roma");
        sede1.setVia("Via Roma");
        sede1.setCivico(1);
        sede1.setCap("00100");

        Sede sede2 = new Sede();
        sede2.setIdSede(2);
        sede2.setCitta("Milano");
        sede2.setVia("Via Milano");
        sede2.setCivico(2);
        sede2.setCap("20100");

        Sede sede3 = new Sede();
        sede3.setIdSede(3);
        sede3.setCitta("Firenze");
        sede3.setVia("Via Firenze");
        sede3.setCivico(3);
        sede3.setCap("50100");

        Reparto reparto1 = new Reparto();
        reparto1.setIdReparto(1);
        reparto1.setNome("Tecnologia");
        reparto1.setDescrizione("Tech");

        Reparto reparto2 = new Reparto();
        reparto2.setIdReparto(2);
        reparto2.setNome("Scienze");
        reparto2.setDescrizione("Science");

        List<Sede> sediPresenti = new ArrayList<>();
        sediPresenti.add(sede1);
        sediPresenti.add(sede2);

        List<Sede> tuteleSedi = new ArrayList<>();
        tuteleSedi.add(sede1);
        tuteleSedi.add(sede2);
        tuteleSedi.add(sede3);

        List<Reparto> repartiPresenti = new ArrayList<>();
        repartiPresenti.add(reparto1);

        List<Reparto> tuttiReparti = new ArrayList<>();
        tuttiReparti.add(reparto1);
        tuttiReparti.add(reparto2);

        when(request.getParameter("isbn")).thenReturn(isbn);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/prodotti/modificaLibro.jsp"))
                .thenReturn(dispatcher);

        try (MockedConstruction<LibroDAO> mockedLibroDAO = mockConstruction(LibroDAO.class, 
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                    when(mock.getPresenzaSede(isbn)).thenReturn(new ArrayList<>(sediPresenti));
                    when(mock.getAppartenenzaReparto(isbn)).thenReturn(new ArrayList<>(repartiPresenti));
                });
             MockedConstruction<SedeDAO> mockedSedeDAO = mockConstruction(SedeDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(tuteleSedi));
                });
             MockedConstruction<RepartoDAO> mockedRepartoDAO = mockConstruction(RepartoDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(tuttiReparti));
                })) {

            // Act
            ModificaLibroServlet servlet = new ModificaLibroServlet();
            servlet.doGet(request, response);

            // Assert - verify all attributes were set with correct counts
            verify(request).setAttribute(eq("libro"), any(Libro.class));
            verify(request, times(1)).setAttribute(eq("sedi"), any(List.class));
            verify(request, times(1)).setAttribute(eq("reparti"), any(List.class));
            verify(request, times(1)).setAttribute(eq("sediNonPresenti"), any(List.class));
            verify(request, times(1)).setAttribute(eq("repartiNonPresenti"), any(List.class));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test case: Valid ISBN but book has no associated locations (sedi)
     */
    @Test
    public void testDoGet_ValidISBN_NoAssociatedSedi() throws Exception {
        // Arrange
        String isbn = "978-0-13-110362-7";

        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setTitolo("The Pragmatic Programmer");

        Sede sede1 = new Sede();
        sede1.setIdSede(1);
        sede1.setCitta("Roma");
        sede1.setVia("Via Roma");
        sede1.setCivico(1);
        sede1.setCap("00100");

        Sede sede2 = new Sede();
        sede2.setIdSede(2);
        sede2.setCitta("Milano");
        sede2.setVia("Via Milano");
        sede2.setCivico(2);
        sede2.setCap("20100");

        Reparto reparto1 = new Reparto();
        reparto1.setIdReparto(1);
        reparto1.setNome("Tecnologia");
        reparto1.setDescrizione("Tech");

        List<Sede> sediPresenti = new ArrayList<>(); // Empty list
        List<Sede> tutteSedi = new ArrayList<>();
        tutteSedi.add(sede1);
        tutteSedi.add(sede2);

        List<Reparto> repartiPresenti = new ArrayList<>();
        repartiPresenti.add(reparto1);

        List<Reparto> tuttiReparti = new ArrayList<>();
        tuttiReparti.add(reparto1);

        when(request.getParameter("isbn")).thenReturn(isbn);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/prodotti/modificaLibro.jsp"))
                .thenReturn(dispatcher);

        try (MockedConstruction<LibroDAO> mockedLibroDAO = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                    when(mock.getPresenzaSede(isbn)).thenReturn(new ArrayList<>(sediPresenti));
                    when(mock.getAppartenenzaReparto(isbn)).thenReturn(new ArrayList<>(repartiPresenti));
                });
             MockedConstruction<SedeDAO> mockedSedeDAO = mockConstruction(SedeDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(tutteSedi));
                });
             MockedConstruction<RepartoDAO> mockedRepartoDAO = mockConstruction(RepartoDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(tuttiReparti));
                })) {

            // Act
            ModificaLibroServlet servlet = new ModificaLibroServlet();
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("libro"), any(Libro.class));
            verify(request).setAttribute(eq("sedi"), argThat(l -> ((List<?>) l).isEmpty()));
            verify(request).setAttribute(eq("sediNonPresenti"), argThat(l -> ((List<?>) l).size() == 2));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test case: Valid ISBN but book has no associated departments (reparti)
     */
    @Test
    public void testDoGet_ValidISBN_NoAssociatedReparti() throws Exception {
        // Arrange
        String isbn = "978-0-13-468599-1";

        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setTitolo("Refactoring");

        Sede sede1 = new Sede();
        sede1.setIdSede(1);
        sede1.setCitta("Roma");
        sede1.setVia("Via Roma");
        sede1.setCivico(1);
        sede1.setCap("00100");

        Reparto reparto1 = new Reparto();
        reparto1.setIdReparto(1);
        reparto1.setNome("Tecnologia");
        reparto1.setDescrizione("Tech");

        Reparto reparto2 = new Reparto();
        reparto2.setIdReparto(2);
        reparto2.setNome("Scienze");
        reparto2.setDescrizione("Science");

        List<Sede> sediPresenti = new ArrayList<>();
        sediPresenti.add(sede1);

        List<Sede> tutteSedi = new ArrayList<>();
        tutteSedi.add(sede1);

        List<Reparto> repartiPresenti = new ArrayList<>(); // Empty list
        List<Reparto> tuttiReparti = new ArrayList<>();
        tuttiReparti.add(reparto1);
        tuttiReparti.add(reparto2);

        when(request.getParameter("isbn")).thenReturn(isbn);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/prodotti/modificaLibro.jsp"))
                .thenReturn(dispatcher);

        try (MockedConstruction<LibroDAO> mockedLibroDAO = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                    when(mock.getPresenzaSede(isbn)).thenReturn(new ArrayList<>(sediPresenti));
                    when(mock.getAppartenenzaReparto(isbn)).thenReturn(new ArrayList<>(repartiPresenti));
                });
             MockedConstruction<SedeDAO> mockedSedeDAO = mockConstruction(SedeDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(tutteSedi));
                });
             MockedConstruction<RepartoDAO> mockedRepartoDAO = mockConstruction(RepartoDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(tuttiReparti));
                })) {

            // Act
            ModificaLibroServlet servlet = new ModificaLibroServlet();
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("libro"), any(Libro.class));
            verify(request).setAttribute(eq("reparti"), argThat(l -> ((List<?>) l).isEmpty()));
            verify(request).setAttribute(eq("repartiNonPresenti"), argThat(l -> ((List<?>) l).size() == 2));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test case: Book is in all available locations and departments
     */
    @Test
    public void testDoGet_BookInAllSediAndReparti() throws Exception {
        // Arrange
        String isbn = "978-0-596-00712-6";

        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setTitolo("Design Patterns");

        Sede sede1 = new Sede();
        sede1.setIdSede(1);
        sede1.setCitta("Roma");
        sede1.setVia("Via Roma");
        sede1.setCivico(1);
        sede1.setCap("00100");

        Sede sede2 = new Sede();
        sede2.setIdSede(2);
        sede2.setCitta("Milano");
        sede2.setVia("Via Milano");
        sede2.setCivico(2);
        sede2.setCap("20100");

        Reparto reparto1 = new Reparto();
        reparto1.setIdReparto(1);
        reparto1.setNome("Tecnologia");
        reparto1.setDescrizione("Tech");

        List<Sede> sediPresenti = new ArrayList<>();
        sediPresenti.add(sede1);
        sediPresenti.add(sede2);

        List<Reparto> repartiPresenti = new ArrayList<>();
        repartiPresenti.add(reparto1);

        when(request.getParameter("isbn")).thenReturn(isbn);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/prodotti/modificaLibro.jsp"))
                .thenReturn(dispatcher);

        try (MockedConstruction<LibroDAO> mockedLibroDAO = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                    when(mock.getPresenzaSede(isbn)).thenReturn(new ArrayList<>(sediPresenti));
                    when(mock.getAppartenenzaReparto(isbn)).thenReturn(new ArrayList<>(repartiPresenti));
                });
             MockedConstruction<SedeDAO> mockedSedeDAO = mockConstruction(SedeDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(sediPresenti));
                });
             MockedConstruction<RepartoDAO> mockedRepartoDAO = mockConstruction(RepartoDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(repartiPresenti));
                })) {

            // Act
            ModificaLibroServlet servlet = new ModificaLibroServlet();
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("libro"), any(Libro.class));
            verify(request, times(1)).setAttribute(eq("sediNonPresenti"), any(List.class));
            verify(request, times(1)).setAttribute(eq("repartiNonPresenti"), any(List.class));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test case: Multiple sedi and reparti with partial associations
     */
    @Test
    public void testDoGet_MultipleSediAndReparti_PartialAssociations() throws Exception {
        // Arrange
        String isbn = "978-1-491-95023-3";

        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setTitolo("Advanced Java");

        List<Sede> sediPresenti = new ArrayList<>();
        for (int i = 1; i <= 2; i++) {
            Sede sede = new Sede();
            sede.setIdSede(i);
            sede.setCitta("City" + i);
            sede.setVia("Via" + i);
            sede.setCivico(i);
            sede.setCap("0000" + i);
            sediPresenti.add(sede);
        }

        List<Sede> tutteSedi = new ArrayList<>();
        for (int i = 1; i <= 5; i++) {
            Sede sede = new Sede();
            sede.setIdSede(i);
            sede.setCitta("City" + i);
            sede.setVia("Via" + i);
            sede.setCivico(i);
            sede.setCap("0000" + i);
            tutteSedi.add(sede);
        }

        List<Reparto> repartiPresenti = new ArrayList<>();
        for (int i = 1; i <= 2; i++) {
            Reparto reparto = new Reparto();
            reparto.setIdReparto(i);
            reparto.setNome("Reparto" + i);
            reparto.setDescrizione("Desc" + i);
            repartiPresenti.add(reparto);
        }

        List<Reparto> tuttiReparti = new ArrayList<>();
        for (int i = 1; i <= 4; i++) {
            Reparto reparto = new Reparto();
            reparto.setIdReparto(i);
            reparto.setNome("Reparto" + i);
            reparto.setDescrizione("Desc" + i);
            tuttiReparti.add(reparto);
        }

        when(request.getParameter("isbn")).thenReturn(isbn);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/prodotti/modificaLibro.jsp"))
                .thenReturn(dispatcher);

        try (MockedConstruction<LibroDAO> mockedLibroDAO = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                    when(mock.getPresenzaSede(isbn)).thenReturn(new ArrayList<>(sediPresenti));
                    when(mock.getAppartenenzaReparto(isbn)).thenReturn(new ArrayList<>(repartiPresenti));
                });
             MockedConstruction<SedeDAO> mockedSedeDAO = mockConstruction(SedeDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(tutteSedi));
                });
             MockedConstruction<RepartoDAO> mockedRepartoDAO = mockConstruction(RepartoDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(tuttiReparti));
                })) {

            // Act
            ModificaLibroServlet servlet = new ModificaLibroServlet();
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("libro"), any(Libro.class));
            verify(request, times(1)).setAttribute(eq("sedi"), argThat(l -> ((List<?>) l).size() == 2));
            verify(request, times(1)).setAttribute(eq("reparti"), argThat(l -> ((List<?>) l).size() == 2));
            verify(request, times(1)).setAttribute(eq("sediNonPresenti"), argThat(l -> ((List<?>) l).size() >= 3));
            verify(request, times(1)).setAttribute(eq("repartiNonPresenti"), argThat(l -> ((List<?>) l).size() >= 2));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test case: doPost method delegates to doGet
     */
    @Test
    public void testDoPost_DelegatesTo_DoGet() throws Exception {
        // Arrange
        String isbn = "978-1-593-27466-9";

        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setTitolo("Code Complete");

        Sede sede = new Sede();
        sede.setIdSede(1);
        sede.setCitta("Roma");
        sede.setVia("Via Roma");
        sede.setCivico(1);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(1);
        reparto.setNome("Tecnologia");
        reparto.setDescrizione("Tech");

        List<Sede> sediList = new ArrayList<>();
        sediList.add(sede);
        List<Reparto> repartoList = new ArrayList<>();
        repartoList.add(reparto);

        when(request.getParameter("isbn")).thenReturn(isbn);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/prodotti/modificaLibro.jsp"))
                .thenReturn(dispatcher);

        try (MockedConstruction<LibroDAO> mockedLibroDAO = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                    when(mock.getPresenzaSede(isbn)).thenReturn(new ArrayList<>(sediList));
                    when(mock.getAppartenenzaReparto(isbn)).thenReturn(new ArrayList<>(repartoList));
                });
             MockedConstruction<SedeDAO> mockedSedeDAO = mockConstruction(SedeDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(sediList));
                });
             MockedConstruction<RepartoDAO> mockedRepartoDAO = mockConstruction(RepartoDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>(repartoList));
                })) {

            // Act
            ModificaLibroServlet servlet = new ModificaLibroServlet();
            servlet.doPost(request, response);

            // Assert - verify same behavior as doGet
            verify(request).setAttribute(eq("libro"), any(Libro.class));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test case: Empty database state (no sedi or reparti exist)
     */
    @Test
    public void testDoGet_EmptyDatabase() throws Exception {
        // Arrange
        String isbn = "978-0-201-63361-0";

        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setTitolo("UML Distilled");

        when(request.getParameter("isbn")).thenReturn(isbn);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/prodotti/modificaLibro.jsp"))
                .thenReturn(dispatcher);

        try (MockedConstruction<LibroDAO> mockedLibroDAO = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                    when(mock.getPresenzaSede(isbn)).thenReturn(new ArrayList<>());
                    when(mock.getAppartenenzaReparto(isbn)).thenReturn(new ArrayList<>());
                });
             MockedConstruction<SedeDAO> mockedSedeDAO = mockConstruction(SedeDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
                });
             MockedConstruction<RepartoDAO> mockedRepartoDAO = mockConstruction(RepartoDAO.class,
                (mock, context) -> {
                    when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
                })) {

            // Act
            ModificaLibroServlet servlet = new ModificaLibroServlet();
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("libro", libro);
            verify(request).setAttribute(eq("sedi"), argThat(list -> ((List<?>) list).size() == 0));
            verify(request).setAttribute(eq("reparti"), argThat(list -> ((List<?>) list).size() == 0));
            verify(request).setAttribute(eq("sediNonPresenti"), argThat(list -> ((List<?>) list).size() == 0));
            verify(request).setAttribute(eq("repartiNonPresenti"), argThat(list -> ((List<?>) list).size() == 0));
            verify(dispatcher).forward(request, response);
        }
    }
}
