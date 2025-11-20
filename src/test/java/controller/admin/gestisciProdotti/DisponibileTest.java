package controller.admin.gestisciProdotti;

import model.libroService.Libro;
import model.libroService.LibroDAO;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import static org.mockito.Mockito.*;
import org.mockito.InOrder;

public class DisponibileTest {

    @Test
    public void validIsbn_marksLibroAsDisponibile_forwardsToGestisciProdotti() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        String testIsbn = "ISBN123456";
        when(request.getParameter("isbn")).thenReturn(testIsbn);
        when(request.getRequestDispatcher("gestisci-prodotti")).thenReturn(dispatcher);

        Libro mockLibro = new Libro();
        mockLibro.setIsbn(testIsbn);
        mockLibro.setDisponibile(false); // Initially not available

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(testIsbn)).thenReturn(mockLibro);
                })) {

            new Disponibile().doGet(request, response);

            // Verify that the libro was retrieved
            boolean retrieved = false;
            for (LibroDAO dao : mocked.constructed()) {
                try {
                    verify(dao, times(1)).doRetrieveById(testIsbn);
                    retrieved = true;
                } catch (Throwable t) {
                    // ignore
                }
            }
            assert(retrieved);

            // Verify that updateDisponibile was called
            boolean updated = false;
            for (LibroDAO dao : mocked.constructed()) {
                try {
                    verify(dao, times(1)).updateDisponibile(argThat(l -> 
                        l.getIsbn().equals(testIsbn) && l.isDisponibile()
                    ));
                    updated = true;
                } catch (Throwable t) {
                    // ignore
                }
            }
            assert(updated);

            // Verify forward to gestisci-prodotti
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void libroAvailabilitySetToTrue() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        String testIsbn = "ISBN789456";
        when(request.getParameter("isbn")).thenReturn(testIsbn);
        when(request.getRequestDispatcher("gestisci-prodotti")).thenReturn(dispatcher);

        Libro mockLibro = new Libro();
        mockLibro.setIsbn(testIsbn);
        mockLibro.setDisponibile(false);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(testIsbn)).thenReturn(mockLibro);
                })) {

            new Disponibile().doGet(request, response);

            // Verify that the libro's disponibile field was set to true
            assert(mockLibro.isDisponibile());
        }
    }

    @Test
    public void requestParameterIsbnRetrieved() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        String testIsbn = "ISBN111222";
        when(request.getParameter("isbn")).thenReturn(testIsbn);
        when(request.getRequestDispatcher("gestisci-prodotti")).thenReturn(dispatcher);

        Libro mockLibro = new Libro();
        mockLibro.setIsbn(testIsbn);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(testIsbn)).thenReturn(mockLibro);
                })) {

            new Disponibile().doGet(request, response);

            // Verify that request parameter isbn was accessed
            verify(request, times(1)).getParameter("isbn");
        }
    }

    @Test
    public void forwardsToCorrectPage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        String testIsbn = "ISBN333444";
        when(request.getParameter("isbn")).thenReturn(testIsbn);
        when(request.getRequestDispatcher("gestisci-prodotti")).thenReturn(dispatcher);

        Libro mockLibro = new Libro();
        mockLibro.setIsbn(testIsbn);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(testIsbn)).thenReturn(mockLibro);
                })) {

            new Disponibile().doGet(request, response);

            // Verify correct page requested
            verify(request, times(1)).getRequestDispatcher("gestisci-prodotti");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void multipleCallsWithDifferentIsbns() throws Exception {
        String[] isbns = {"ISBN001", "ISBN002", "ISBN003"};

        for (String isbn : isbns) {
            HttpServletRequest request = mock(HttpServletRequest.class);
            HttpServletResponse response = mock(HttpServletResponse.class);
            RequestDispatcher dispatcher = mock(RequestDispatcher.class);

            when(request.getParameter("isbn")).thenReturn(isbn);
            when(request.getRequestDispatcher("gestisci-prodotti")).thenReturn(dispatcher);

            Libro mockLibro = new Libro();
            mockLibro.setIsbn(isbn);
            mockLibro.setDisponibile(false);

            try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                    (mock, context) -> {
                        when(mock.doRetrieveById(isbn)).thenReturn(mockLibro);
                    })) {

                new Disponibile().doGet(request, response);

                // Each request should result in forward
                verify(dispatcher, times(1)).forward(request, response);
                assert(mockLibro.isDisponibile());
            }
        }
    }

    @Test
    public void libroDAOUpdateDisponibileCalledAfterRetrieval() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        String testIsbn = "ISBN555666";
        when(request.getParameter("isbn")).thenReturn(testIsbn);
        when(request.getRequestDispatcher("gestisci-prodotti")).thenReturn(dispatcher);

        Libro mockLibro = new Libro();
        mockLibro.setIsbn(testIsbn);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(testIsbn)).thenReturn(mockLibro);
                })) {

            new Disponibile().doGet(request, response);

            boolean updateCalled = false;
            for (LibroDAO dao : mocked.constructed()) {
                try {
                    // Verify the order: retrieve should happen, then update
                    InOrder inOrder = inOrder(dao);
                    inOrder.verify(dao).doRetrieveById(testIsbn);
                    inOrder.verify(dao).updateDisponibile(any(Libro.class));
                    updateCalled = true;
                } catch (Throwable t) {
                    // ignore
                }
            }
            assert(updateCalled);
        }
    }

    @Test
    public void libroWithCompleteData_stillUpdatesDisponibile() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        String testIsbn = "ISBN777888";
        when(request.getParameter("isbn")).thenReturn(testIsbn);
        when(request.getRequestDispatcher("gestisci-prodotti")).thenReturn(dispatcher);

        Libro mockLibro = new Libro();
        mockLibro.setIsbn(testIsbn);
        mockLibro.setTitolo("Test Book");
        mockLibro.setGenere("Fiction");
        mockLibro.setPrezzo(19.99);
        mockLibro.setSconto(10);
        mockLibro.setDisponibile(false);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(testIsbn)).thenReturn(mockLibro);
                })) {

            new Disponibile().doGet(request, response);

            // Verify that updateDisponibile was called with the libro
            boolean updated = false;
            for (LibroDAO dao : mocked.constructed()) {
                try {
                    verify(dao, times(1)).updateDisponibile(mockLibro);
                    updated = true;
                } catch (Throwable t) {
                    // ignore
                }
            }
            assert(updated);
            assert(mockLibro.isDisponibile());
        }
    }
}
